//! Manages an individual TCP connection between the relay and an internet server.
//! Implements a TCP state machine to translate between the device's virtual TCP
//! and the real TCP socket on the host.

use log::*;
use rand::random;
use socket2::{Domain, SockRef, Socket, TcpKeepalive, Type};
use std::cell::RefCell;
use std::cmp;
use std::io;
use std::net::TcpStream;
use std::num::Wrapping;
use std::rc::{Rc, Weak};
use std::time::Duration;

use super::binary;
use super::client::{Client, ClientChannel, SharedBuffer};
use super::connection::{Connection, ConnectionId};
use super::ip_header::IpHeader;
use super::ip_packet::IpPacket;
use super::ipv4_packet::MAX_PACKET_LENGTH;
use super::packetizer::Packetizer;
use super::stream_buffer::StreamBuffer;
use super::tcp_header::{self, TcpHeader, TcpHeaderData, TcpHeaderMut};
use super::transport_header::{TransportHeader, TransportHeaderMut};
use std::sync::OnceLock;

const TAG: &str = "TcpConnection";

/// Global SOCKS5 proxy address, set at startup by the CLI `--socks5` flag.
pub static SOCKS5_PROXY: OnceLock<std::net::SocketAddr> = OnceLock::new();

/// Largest payload sent to the device when its SYN announces no MSS: what a 1500-byte MTU allows.
const DEFAULT_MAX_PAYLOAD_LENGTH: u16 = 1500 - 20 - 20;

/// Largest payload that keeps a packet's length within 16 bits with any IP header.
const MAX_PAYLOAD_LENGTH: u16 = u16::MAX - 40 - 20;

/// Bytes read from the server per poll, at most (plus one segment).
const MAX_BYTES_PER_POLL: usize = 32 * DEFAULT_MAX_PAYLOAD_LENGTH as usize;

/// Capacity of the buffer holding data from the device not yet written to the network. The
/// window advertised to the device describes the free space in this buffer.
const CLIENT_TO_NETWORK_CAPACITY: usize = 32 * MAX_PACKET_LENGTH;

#[allow(dead_code)]
pub static mut GLOBAL_BYTES_SENT: u64 = 0;
#[allow(dead_code)]
pub static mut GLOBAL_BYTES_RECEIVED: u64 = 0;

pub struct TcpConnection {
    #[allow(dead_code)]
    self_weak: Weak<RefCell<TcpConnection>>,
    id: ConnectionId,
    client: Weak<RefCell<Client>>,
    /// Shared outgoing buffer. Writing here goes straight to the device
    /// without needing to borrow the `Client`.
    buffer: SharedBuffer,
    stream: TcpStream,
    client_to_network: StreamBuffer,
    network_to_client: Packetizer,
    /// Length of a packet that could not be written to the buffer yet
    /// (because the buffer was full). It is retried on each poll.
    packet_for_client_length: Option<u16>,
    /// Packetizer for the SYN-ACK when the device asked for window scaling: the
    /// SYN-ACK must carry a Window Scale option, which the main packetizer's
    /// 20-byte header cannot hold. Dropped once the SYN-ACK is sent.
    syn_ack_packetizer: Option<Packetizer>,
    closed: bool,
    tcb: Tcb,
    /// Largest payload of a segment to the device: the MSS of its SYN.
    max_payload_length: u16,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

struct Tcb {
    state: TcpState,
    syn_sequence_number: u32,
    sequence_number: Wrapping<u32>,
    acknowledgement_number: Wrapping<u32>,
    their_acknowledgement_number: u32,
    fin_sequence_number: Option<u32>,
    fin_received: bool,
    /// Receive window of the device, in bytes (already scaled).
    client_window: u32,
    /// Shift applied to the window field of the device's segments (RFC 7323).
    client_window_scale: u8,
    /// Shift applied to the window field of the relay's segments (RFC 7323).
    relay_window_scale: u8,
}

#[derive(Debug, PartialEq, Eq)]
enum TcpState {
    Init,
    SynSent,
    SynReceived,
    Established,
    LastAck,
    Closing,
    FinWait1,
    FinWait2,
}

impl TcpState {
    #[inline]
    fn is_connected(&self) -> bool {
        !matches!(self, TcpState::Init | TcpState::SynSent | TcpState::SynReceived)
    }

    #[inline]
    fn is_closed(&self) -> bool {
        matches!(
            self,
            TcpState::FinWait1 | TcpState::FinWait2 | TcpState::Closing | TcpState::LastAck
        )
    }
}

impl Tcb {
    fn new() -> Self {
        Self {
            state: TcpState::Init,
            syn_sequence_number: 0,
            sequence_number: Wrapping(0),
            acknowledgement_number: Wrapping(0),
            their_acknowledgement_number: 0,
            fin_sequence_number: None,
            fin_received: false,
            client_window: 0,
            client_window_scale: 0,
            relay_window_scale: 0,
        }
    }

    #[inline]
    fn remaining_client_window(&self) -> u32 {
        // If the client advertised a zero window, honor it immediately.
        if self.client_window == 0 {
            return 0;
        }

        let wrapped_remaining =
            Wrapping(self.their_acknowledgement_number) + Wrapping(self.client_window) - self.sequence_number;
        let remaining = wrapped_remaining.0;
        if remaining <= self.client_window { remaining } else { 0 }
    }

    fn numbers(&self) -> String {
        format!("(seq={}, ack={})", self.sequence_number, self.acknowledgement_number)
    }
}

/// Largest payload of a segment to the device, given the MSS option of its SYN.
///
/// The device announces the MSS its VPN interface allows (16344 bytes for the client's 16384-byte
/// MTU). Every segment costs the client a write to that interface, so sending 1460-byte segments
/// to such a device multiplies its work per byte by 11.
fn max_payload_length_for(mss: Option<u16>) -> u16 {
    match mss {
        Some(mss) if mss > 0 => mss.min(MAX_PAYLOAD_LENGTH),
        _ => DEFAULT_MAX_PAYLOAD_LENGTH,
    }
}

/// Smallest RFC 7323 shift count that lets a 16-bit window field describe `capacity` bytes.
fn window_scale_for(capacity: usize) -> u8 {
    let mut shift = 0;
    while shift < tcp_header::MAX_WINDOW_SCALE && (capacity >> shift) > usize::from(u16::MAX) {
        shift += 1;
    }
    shift
}

/// Value of the 16-bit window field describing `bytes` of free space, for the given shift count.
fn scaled_window(bytes: usize, shift: u8) -> u16 {
    (bytes >> shift).min(usize::from(u16::MAX)) as u16
}

/// Start connecting to `destination` without waiting for the handshake.
///
/// Every connection of a client is polled from one thread, so a blocking connect would stall all
/// of them (including established streams) until the server answers, or until the OS connect
/// timeout when it never does. `connect_status()` reports when the connection completes.
fn connect_nonblocking(destination: &std::net::SocketAddr) -> io::Result<TcpStream> {
    let socket = Socket::new(
        Domain::for_address(*destination),
        Type::STREAM,
        Some(socket2::Protocol::TCP),
    )?;
    socket.set_nonblocking(true)?;
    match socket.connect(&(*destination).into()) {
        Ok(()) => {}
        Err(ref err) if is_connect_in_progress(err) => {}
        Err(err) => return Err(err),
    }
    Ok(socket.into())
}

fn is_connect_in_progress(err: &io::Error) -> bool {
    // Unix reports EINPROGRESS. Windows reports WSAEWOULDBLOCK, which maps to WouldBlock.
    #[cfg(unix)]
    {
        if err.raw_os_error() == Some(libc::EINPROGRESS) {
            return true;
        }
    }
    err.kind() == io::ErrorKind::WouldBlock
}

/// State of a non-blocking connect: `Ok(true)` once established, `Ok(false)` while the handshake
/// is in progress, `Err` if it failed.
fn connect_status(stream: &TcpStream) -> io::Result<bool> {
    if let Some(err) = stream.take_error()? {
        return Err(err);
    }
    match stream.peer_addr() {
        Ok(_) => Ok(true),
        Err(ref err) if err.kind() == io::ErrorKind::NotConnected => Ok(false),
        Err(err) => Err(err),
    }
}

/// Receive buffer of the socket to the server. Data the device cannot take yet waits in it, so
/// beyond what keeps the relay fed, a larger buffer only adds delay. A server on the local network
/// answers in well under a millisecond and needs little: with 1 MiB, bursts from a Virtual Desktop
/// streamer on the host queued ~1.5 MB (~45 ms) inside the relay. Internet servers keep 1 MiB to
/// cover their bandwidth-delay product.
fn recv_buffer_size(destination: &std::net::SocketAddr) -> usize {
    if is_local_network(destination.ip()) {
        256 * 1024
    } else {
        1024 * 1024
    }
}

fn is_local_network(ip: std::net::IpAddr) -> bool {
    match ip {
        std::net::IpAddr::V4(v4) => v4.is_loopback() || v4.is_private() || v4.is_link_local(),
        std::net::IpAddr::V6(v6) => v6.is_loopback() || v6.is_unique_local() || v6.is_unicast_link_local(),
    }
}

/// Build the SOCKS5 CONNECT request (RFC 1928 §4) for the given destination.
///
/// The request layout is:
/// ```text
///   +----+-----+-------+------+----------+----------+
///   |VER | CMD |  RSV  | ATYP | DST.ADDR | DST.PORT |
///   +----+-----+-------+------+----------+----------+
///   | 1  |  1  | X'00' |  1   | Variable |    2     |
///   +----+-----+-------+------+----------+----------+
/// ```
///
/// `ATYP` must match the destination address family:
///   * `0x01` — IPv4 (4-byte address)
///   * `0x04` — IPv6 (16-byte address)
///
/// `DST.PORT` is always 2 bytes, big-endian.
fn build_socks5_connect_request(destination: &std::net::SocketAddr) -> Vec<u8> {
    let port_be = destination.port().to_be_bytes();
    let mut request = vec![0x05, 0x01, 0x00]; // VER=5, CMD=CONNECT, RSV=0
    match destination.ip() {
        std::net::IpAddr::V4(ip) => {
            request.push(0x01); // ATYP = IPv4
            request.extend_from_slice(&ip.octets());
        }
        std::net::IpAddr::V6(ip) => {
            request.push(0x04); // ATYP = IPv6
            request.extend_from_slice(&ip.octets());
        }
    }
    request.extend_from_slice(&port_be);
    request
}

impl TcpConnection {
    #[allow(clippy::needless_pass_by_value)] // semantically, headers are consumed
    pub fn create(
        id: ConnectionId,
        client: Weak<RefCell<Client>>,
        buffer: SharedBuffer,
        ip_header: IpHeader,
        transport_header: TransportHeader,
    ) -> io::Result<Rc<RefCell<Self>>> {
        cx_info!(target: TAG, id, "Open");
        let stream = Self::create_stream(&id)?;

        let tcp_header = Self::tcp_header_of_transport(transport_header);
        let packetizer = Self::create_packetizer(&ip_header, &tcp_header);

        // RFC 7323: window scaling is in effect only if both the SYN and the SYN-ACK carry the
        // option. Without it, the device can never have more than 64 KiB unacknowledged, which caps
        // each connection at 64 KiB per round trip.
        let client_window_scale = if tcp_header.is_syn() {
            tcp_header.window_scale()
        } else {
            None
        };
        let relay_window_scale = window_scale_for(CLIENT_TO_NETWORK_CAPACITY);
        let max_payload_length = max_payload_length_for(if tcp_header.is_syn() { tcp_header.mss() } else { None });
        let syn_ack_packetizer =
            client_window_scale.map(|_| Self::create_syn_ack_packetizer(&ip_header, &tcp_header, relay_window_scale));
        let mut tcb = Tcb::new();
        if let Some(scale) = client_window_scale {
            cx_debug!(
                target: TAG,
                id,
                "Window scaling: client shift={}, relay shift={}",
                scale,
                relay_window_scale
            );
            tcb.client_window_scale = scale;
            tcb.relay_window_scale = relay_window_scale;
        }

        let rc = Rc::new(RefCell::new(Self {
            self_weak: Weak::new(),
            id,
            client,
            buffer,
            stream,
            client_to_network: StreamBuffer::new(CLIENT_TO_NETWORK_CAPACITY),
            network_to_client: packetizer,
            packet_for_client_length: None,
            syn_ack_packetizer,
            closed: false,
            tcb,
            max_payload_length,
            bytes_sent: 0,
            bytes_received: 0,
        }));

        {
            let mut self_ref = rc.borrow_mut();
            self_ref.self_weak = Rc::downgrade(&rc);
        }
        Ok(rc)
    }

    /// Packetizer for packets to the device: the headers of `tcp_header` with source and
    /// destination swapped and no TCP options.
    fn create_packetizer(ip_header: &IpHeader, tcp_header: &TcpHeader) -> Packetizer {
        // shrink the TCP options to pass a minimal reference header to the packetizer
        let mut shrinked_tcp_header_raw = [0u8; 20];
        shrinked_tcp_header_raw.copy_from_slice(&tcp_header.raw()[..20]);
        let mut shrinked_tcp_header_data = tcp_header.data().clone();
        {
            let mut shrinked_tcp_header = shrinked_tcp_header_data.bind_mut(&mut shrinked_tcp_header_raw);
            shrinked_tcp_header.shrink_options();
            debug_assert_eq!(20, shrinked_tcp_header.header_length());
        }

        let shrinked_transport_header = shrinked_tcp_header_data.bind(&shrinked_tcp_header_raw).into();
        Packetizer::new(ip_header, &shrinked_transport_header)
    }

    /// RST answering a SYN the relay cannot connect, so the device fails the connect at once
    /// (and tries its next address, e.g. IPv4 after IPv6) instead of waiting for its SYN
    /// retransmissions to time out. `None` if the packet is not a SYN.
    pub fn reset_for_syn(ip_packet: &IpPacket) -> Option<Vec<u8>> {
        let (ip_header, Some(TransportHeader::Tcp(tcp_header))) = ip_packet.headers() else {
            return None;
        };
        if !tcp_header.is_syn() || tcp_header.is_ack() {
            return None;
        }
        let mut packetizer = Self::create_packetizer(&ip_header, &tcp_header);
        // RFC 9293 §3.10.7.1: the SYN carries no ACK, so the RST has sequence number 0 and must
        // acknowledge the SYN, or the device ignores it.
        let mut tcb = Tcb::new();
        tcb.acknowledgement_number = Wrapping(tcp_header.sequence_number()) + Wrapping(1);
        Self::update_headers(&mut packetizer, &tcb, tcp_header::FLAG_RST | tcp_header::FLAG_ACK, 0);
        Some(packetizer.packetize_empty_payload().raw().to_vec())
    }

    /// Packetizer for the SYN-ACK only: same headers as the main packetizer, plus a Window Scale
    /// option announcing `relay_window_scale`.
    fn create_syn_ack_packetizer(ip_header: &IpHeader, tcp_header: &TcpHeader, relay_window_scale: u8) -> Packetizer {
        let raw = tcp_header::header_with_window_scale(tcp_header.raw(), relay_window_scale);
        let data = TcpHeaderData::parse(&raw);
        let transport_header: TransportHeader = data.bind(&raw).into();
        Packetizer::new(ip_header, &transport_header)
    }

    fn create_stream(id: &ConnectionId) -> io::Result<TcpStream> {
        let dest = id.rewritten_destination();
        let stream = if let Some(proxy) = SOCKS5_PROXY.get() {
            Self::connect_via_socks5(proxy, &dest)?
        } else {
            connect_nonblocking(&dest)?
        };
        stream.set_nonblocking(true)?;
        stream.set_nodelay(true)?;

        let sock_ref = SockRef::from(&stream);
        let _ = sock_ref.set_recv_buffer_size(recv_buffer_size(&dest));
        let _ = sock_ref.set_send_buffer_size(256 * 1024);

        let ka = TcpKeepalive::new().with_time(Duration::from_secs(60));
        let _ = sock_ref.set_tcp_keepalive(&ka);

        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            let fd = stream.as_raw_fd();
            let one: libc::c_int = 1;
            unsafe {
                libc::setsockopt(
                    fd,
                    libc::SOL_TCP,
                    libc::TCP_FASTOPEN_CONNECT,
                    &one as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                );
            }
        }

        Ok(stream)
    }

    /// Connect to a destination through a SOCKS5 proxy.
    fn connect_via_socks5(proxy: &std::net::SocketAddr, destination: &std::net::SocketAddr) -> io::Result<TcpStream> {
        use std::io::{Read, Write};
        let mut stream = TcpStream::connect(proxy)?;
        stream.set_nonblocking(false)?;

        // Step 1: method negotiation. We only advertise "no authentication".
        let greeting = [0x05, 0x01, 0x00];
        stream.write_all(&greeting)?;

        let mut response = [0u8; 2];
        stream.read_exact(&mut response)?;
        if response != [0x05, 0x00] {
            return Err(io::Error::other(format!(
                "SOCKS5 handshake failed: expected [0x05, 0x00], got {:?}",
                response
            )));
        }

        // Step 2: send the CONNECT request. ATYP depends on the destination
        // address family (IPv4 → 0x01, IPv6 → 0x04).
        let connect_request = build_socks5_connect_request(destination);
        stream.write_all(&connect_request)?;

        // Step 3: parse the reply.
        let mut reply = [0u8; 4];
        stream.read_exact(&mut reply)?;
        if reply[0] != 0x05 || reply[1] != 0x00 {
            return Err(io::Error::other(format!("SOCKS5 connect failed: reply={:?}", reply)));
        }
        let addr_type = reply[3];
        let remaining_len = match addr_type {
            0x01 => 4 + 2,
            0x03 => {
                let mut len_byte = [0u8; 1];
                stream.read_exact(&mut len_byte)?;
                len_byte[0] as usize + 1 + 2
            }
            0x04 => 16 + 2,
            _ => {
                return Err(io::Error::other(format!("SOCKS5 unknown address type: {}", addr_type)));
            }
        };
        if remaining_len > 0 {
            let mut rest = vec![0u8; remaining_len];
            stream.read_exact(&mut rest)?;
        }

        stream.set_nonblocking(true)?;
        Ok(stream)
    }

    fn remove_from_router(&self) {
        let client_rc = self
            .client
            .upgrade()
            .unwrap_or_else(|| panic!("Expected client not found"));
        let mut client = match client_rc.try_borrow_mut() {
            Ok(c) => c,
            Err(_) => {
                cx_debug!(target: TAG, self.id, "Client busy, skipping");
                return;
            }
        };
        client.router().remove(&self.id);
    }

    /// Write an IP packet into the shared buffer.
    ///
    /// This is intentionally an associated function rather than a `&self`
    /// method: the callers frequently hold a mutable borrow of
    /// `self.network_to_client` (through the `IpPacket` returned by the
    /// packetizer), and a `&self` method would conflict with it. Taking
    /// `&SharedBuffer` explicitly restricts the borrow to the `buffer` field,
    /// which is disjoint from `network_to_client` and therefore accepted by
    /// the borrow checker.
    fn send_packet_to_buffer(buffer: &SharedBuffer, ip_packet: &IpPacket) -> io::Result<()> {
        let mut buf = match buffer.try_borrow_mut() {
            Ok(b) => b,
            Err(_) => {
                return Err(io::Error::new(io::ErrorKind::WouldBlock, "client buffer busy"));
            }
        };
        if ip_packet.length() as usize <= buf.remaining() {
            buf.read_from(ip_packet.raw());
            Ok(())
        } else {
            Err(io::Error::new(io::ErrorKind::WouldBlock, "client buffer full"))
        }
    }

    /// Retry flushing the deferred packet (if any). Called at the top of
    /// `poll_self()` before anything else, so that a packet deferred on a
    /// previous iteration is not stuck forever.
    fn flush_pending_packet(&mut self) -> io::Result<()> {
        let len = match self.packet_for_client_length {
            Some(l) => l,
            None => return Ok(()),
        };
        let ip_packet = self.network_to_client.inflate(len);
        match Self::send_packet_to_buffer(&self.buffer, &ip_packet) {
            Ok(()) => {
                self.tcb.sequence_number += Wrapping(u32::from(len));
                self.packet_for_client_length = None;
                cx_debug!(
                    target: TAG,
                    self.id,
                    "Deferred packet flushed ({} bytes) {}",
                    len,
                    self.tcb.numbers()
                );
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// Poll the connection: try to send/receive on the network socket.
    fn poll_self(&mut self) -> io::Result<()> {
        if self.closed {
            return Ok(());
        }

        let mut made_progress = false;

        // First, retry a previously deferred packet (if any). If it still
        // cannot be flushed, stop here and try again on the next iteration.
        if self.packet_for_client_length.is_some() {
            match self.flush_pending_packet() {
                Ok(()) => made_progress = true,
                Err(ref err) if err.kind() == io::ErrorKind::WouldBlock => {
                    return Err(io::Error::new(
                        io::ErrorKind::WouldBlock,
                        "pending packet still cannot be flushed",
                    ));
                }
                Err(err) => return Err(err),
            }
        }

        if self.may_write() {
            match self.process_send() {
                Ok(()) => made_progress = true,
                Err(ref err) if err.kind() == io::ErrorKind::WouldBlock => {}
                Err(err) => {
                    cx_error!(
                        target: TAG,
                        self.id,
                        "Cannot write: [{:?}] {}",
                        err.kind(),
                        err
                    );
                    self.send_empty_packet_to_client(tcp_header::FLAG_RST);
                    self.close();
                    return Ok(());
                }
            }
        }

        if !self.closed && self.may_read() {
            match self.process_receive() {
                Ok(()) => made_progress = true,
                Err(ref err) if err.kind() == io::ErrorKind::WouldBlock => {}
                Err(err) => {
                    cx_error!(
                        target: TAG,
                        self.id,
                        "Cannot read: [{:?}] {}",
                        err.kind(),
                        err
                    );
                    self.send_empty_packet_to_client(tcp_header::FLAG_RST);
                    self.close();
                    return Ok(());
                }
            }
        }

        if self.tcb.state == TcpState::SynSent {
            match connect_status(&self.stream) {
                Ok(true) => {
                    self.process_connect();
                    made_progress = true;
                }
                Ok(false) => {}
                Err(err) => {
                    cx_error!(
                        target: TAG,
                        self.id,
                        "Cannot connect: [{:?}] {}",
                        err.kind(),
                        err
                    );
                    self.close();
                    return Ok(());
                }
            }
        }

        if self.closed {
            self.remove_from_router();
        }

        if made_progress {
            Ok(())
        } else {
            Err(io::Error::new(io::ErrorKind::WouldBlock, "Connection would block"))
        }
    }

    fn process_send(&mut self) -> io::Result<()> {
        match self.client_to_network.write_to(&mut self.stream) {
            Ok(w) => {
                if w != 0 {
                    self.bytes_sent += w as u64;

                    if self.tcb.fin_received && self.client_to_network.is_empty() {
                        cx_debug!(
                            target: TAG,
                            self.id,
                            "No more pending data, process the pending FIN"
                        );
                        self.do_handle_fin();
                    } else {
                        cx_debug!(
                            target: TAG,
                            self.id,
                            "Sending ACK {} to client",
                            self.tcb.numbers()
                        );
                        self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
                    }
                } else {
                    self.close();
                }
            }
            Err(err) => {
                if err.kind() == io::ErrorKind::WouldBlock {
                    return Err(err);
                }
                cx_error!(
                    target: TAG,
                    self.id,
                    "Cannot write: [{:?}] {}",
                    err.kind(),
                    err
                );
                self.send_empty_packet_to_client(tcp_header::FLAG_RST);
                self.close();
            }
        }
        Ok(())
    }

    fn process_receive(&mut self) -> io::Result<()> {
        // Read as many packets as possible per poll. Reading only one packet
        // per call caps throughput at one packet per client-loop iteration,
        // which forces the remote server's send window closed and starves
        // bulk transfers (speed tests, large downloads). The budget is in
        // bytes so that larger segments do not fill the client buffer faster.
        let mut made_progress = false;
        let mut bytes_read = 0;

        while bytes_read < MAX_BYTES_PER_POLL {
            // If a previous packet could not be flushed to the client buffer,
            // stop reading: we don't want to accumulate more pending data.
            if self.packet_for_client_length.is_some() {
                break;
            }
            if self.tcb.remaining_client_window() == 0 {
                break;
            }
            let remaining_client_window = self.tcb.remaining_client_window();
            let max_payload_length =
                Some(cmp::min(remaining_client_window, u32::from(self.max_payload_length)) as usize);
            let advertised_window = self.advertised_window();
            Self::update_headers(
                &mut self.network_to_client,
                &self.tcb,
                tcp_header::FLAG_ACK | tcp_header::FLAG_PSH,
                advertised_window,
            );
            match self
                .network_to_client
                .packetize_read(&mut self.stream, max_payload_length)
            {
                Ok(Some(ip_packet)) => {
                    self.bytes_received += ip_packet.payload().map(|p| p.len() as u64).unwrap_or(0);
                    match Self::send_packet_to_buffer(&self.buffer, &ip_packet) {
                        Ok(()) => {
                            let len = ip_packet.payload().unwrap().len();
                            cx_debug!(
                                target: TAG,
                                self.id,
                                "Packet ({} bytes) sent to client {}",
                                len,
                                self.tcb.numbers()
                            );
                            self.tcb.sequence_number += Wrapping(len as u32);
                            bytes_read += len;
                            made_progress = true;
                        }
                        Err(_) => {
                            cx_debug!(
                                target: TAG,
                                self.id,
                                "Client buffer unavailable, deferring packet ({} bytes)",
                                ip_packet.length()
                            );
                            self.packet_for_client_length = Some(ip_packet.length());
                            break;
                        }
                    };
                }
                Ok(None) => {
                    self.eof();
                    made_progress = true;
                    break;
                }
                Err(err) => {
                    if err.kind() == io::ErrorKind::WouldBlock {
                        // No more data available right now.
                        break;
                    }
                    cx_error!(
                        target: TAG,
                        self.id,
                        "Cannot read: [{:?}] {}",
                        err.kind(),
                        err
                    );
                    self.send_empty_packet_to_client(tcp_header::FLAG_RST);
                    self.close();
                    made_progress = true;
                    break;
                }
            }
        }

        if made_progress {
            Ok(())
        } else {
            Err(io::Error::new(io::ErrorKind::WouldBlock, "No packet read"))
        }
    }

    fn process_connect(&mut self) {
        debug_assert_eq!(self.tcb.state, TcpState::SynSent);
        self.tcb.state = TcpState::SynReceived;
        cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
        self.send_syn_ack();
        self.tcb.sequence_number += Wrapping(1);
    }

    /// Send the SYN-ACK, with a Window Scale option if the device sent one in its SYN.
    fn send_syn_ack(&mut self) {
        let flags = tcp_header::FLAG_SYN | tcp_header::FLAG_ACK;
        let Some(mut packetizer) = self.syn_ack_packetizer.take() else {
            // no window scaling: relay_window_scale is 0, so the regular path is correct
            self.send_empty_packet_to_client(flags);
            return;
        };
        // RFC 7323 §2.2: the window field of a SYN segment is never scaled.
        let window = scaled_window(self.client_to_network.remaining(), 0);
        let ip_packet = Self::create_empty_response_packet(&self.id, &mut packetizer, &self.tcb, flags, window);
        if Self::send_packet_to_buffer(&self.buffer, &ip_packet).is_err() {
            cx_debug!(target: TAG, self.id, "Buffer unavailable, skipping SYN-ACK");
        }
    }

    /// Send empty packet with the given flags to the client, writing directly
    /// into the shared buffer. No `Client` borrow is performed, so this is safe
    /// to call from within `poll_self()`.
    fn send_empty_packet_to_client(&mut self, flags: u16) {
        let window = self.advertised_window();
    
        // Logging adicional
        if window == 0 {
            cx_warn!(
                target: TAG,
                self.id,
                "Advertising window=0 to client (buffer remaining={})",
                self.client_to_network.remaining()
            );
        }
    
        let ip_packet =
            Self::create_empty_response_packet(&self.id, &mut self.network_to_client, &self.tcb, flags, window);
        match Self::send_packet_to_buffer(&self.buffer, &ip_packet) {
            Ok(()) => {
                cx_debug!(
                    target: TAG,
                    self.id,
                    "Control packet (flags={}, window={}) sent to client",
                    flags, window
                );
            }
            Err(_) => {
                cx_debug!(
                    target: TAG,
                    self.id,
                    "Buffer unavailable, skipping control packet (flags={})",
                    flags
                );
            }
        }
    }

    fn eof(&mut self) {
        cx_debug!(target: TAG, self.id, "EOF");
        self.tcb.acknowledgement_number += Wrapping(1); // FIN counts for 1 byte
        self.send_empty_packet_to_client(tcp_header::FLAG_FIN | tcp_header::FLAG_ACK);
        self.tcb.fin_sequence_number = Some(self.tcb.sequence_number.0);
        self.tcb.sequence_number += Wrapping(1); // FIN counts for 1 byte
        self.tcb.state = TcpState::FinWait1;
        cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
    }

    #[inline]
    fn tcp_header_of_transport(transport_header: TransportHeader) -> TcpHeader {
        if let TransportHeader::Tcp(tcp_header) = transport_header {
            tcp_header
        } else {
            panic!("Not a TCP header");
        }
    }

    #[inline]
    fn tcp_header_of_transport_mut(transport_header: TransportHeaderMut) -> TcpHeaderMut {
        if let TransportHeaderMut::Tcp(tcp_header) = transport_header {
            tcp_header
        } else {
            panic!("Not a TCP header");
        }
    }

    #[inline]
    fn tcp_header_of_packet<'a>(ip_packet: &'a IpPacket) -> TcpHeader<'a> {
        match ip_packet.transport_header() {
            Some(TransportHeader::Tcp(tcp_header)) => tcp_header,
            _ => panic!("Not a TCP packet"),
        }
    }

    fn update_headers(packetizer: &mut Packetizer, tcb: &Tcb, flags: u16, window: u16) {
        let mut tcp_header = Self::tcp_header_of_transport_mut(packetizer.transport_header_mut());
        tcp_header.set_sequence_number(tcb.sequence_number.0);
        tcp_header.set_acknowledgement_number(tcb.acknowledgement_number.0);
        tcp_header.set_flags(flags);
        tcp_header.set_window(window);
    }

    fn handle_packet(&mut self, client_channel: &mut ClientChannel, ip_packet: &IpPacket) {
        let tcp_header = Self::tcp_header_of_packet(ip_packet);
        if self.tcb.state == TcpState::Init {
            self.handle_first_packet(client_channel, ip_packet);
            return;
        }

        if tcp_header.is_syn() {
            self.handle_duplicate_syn(client_channel, ip_packet);
            return;
        }

        let expected_packet = self.tcb.acknowledgement_number.0;
        if tcp_header.sequence_number() != expected_packet {
            // Is this a retransmission? (seq < expected under wraparound arithmetic)
            let diff = tcp_header.sequence_number().wrapping_sub(expected_packet) as i32;
            if diff < 0 {
                // The sender is repeating a segment we already acknowledged.
                // Resend the current ACK so it can make progress.
                cx_debug!(
                    target: TAG,
                    self.id,
                    "Retransmission (seq={} < expected={}); re-ACKing",
                    tcp_header.sequence_number(),
                    expected_packet
                );
                self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
                return;
            }
            cx_warn!(
                target: TAG,
                self.id,
                "Ignoring packet {} (acking {}); expecting {}; flags={}",
                tcp_header.sequence_number(),
                tcp_header.acknowledgement_number(),
                expected_packet,
                tcp_header.flags()
            );
            return;
        }

        let client_window = u32::from(tcp_header.window()) << self.tcb.client_window_scale;
        if client_window != self.tcb.client_window {
            cx_debug!(
                target: TAG,
                self.id,
                "Client window: {} -> {}",
                self.tcb.client_window,
                client_window
            );
        }

        self.tcb.client_window = client_window;
        self.tcb.their_acknowledgement_number = tcp_header.acknowledgement_number();

        cx_debug!(
            target: TAG,
            self.id,
            "Receiving expected packet {} (flags={})",
            tcp_header.sequence_number(),
            tcp_header.flags()
        );

        if tcp_header.is_rst() {
            self.close();
            return;
        }

        if tcp_header.is_ack() {
            cx_debug!(
                target: TAG,
                self.id,
                "Client acked {}",
                tcp_header.acknowledgement_number()
            );

            self.handle_ack(client_channel, ip_packet);
        }

        if tcp_header.is_fin() {
            self.handle_fin(client_channel);
        }

        if let Some(fin_sequence_number) = self.tcb.fin_sequence_number
            && tcp_header.acknowledgement_number() == fin_sequence_number + 1
        {
            cx_debug!(target: TAG, self.id, "Received ACK of FIN");
            self.handle_fin_ack();
        }
    }

    fn handle_first_packet(&mut self, client_channel: &mut ClientChannel, ip_packet: &IpPacket) {
        cx_debug!(target: TAG, self.id, "handle_first_packet()");
        let tcp_header = Self::tcp_header_of_packet(ip_packet);
        if tcp_header.is_syn() {
            let their_sequence_number = tcp_header.sequence_number();
            self.tcb.acknowledgement_number = Wrapping(their_sequence_number) + Wrapping(1);
            self.tcb.syn_sequence_number = their_sequence_number;

            self.tcb.sequence_number = Wrapping(random::<u32>());
            cx_debug!(
                target: TAG,
                self.id,
                "Initialized seq={}; ack={}",
                self.tcb.sequence_number,
                self.tcb.acknowledgement_number
            );
            // RFC 7323 §2.2: the window field of a SYN segment is never scaled.
            self.tcb.client_window = u32::from(tcp_header.window());
            self.tcb.state = TcpState::SynSent;
            cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
        } else {
            cx_warn!(
                target: TAG,
                self.id,
                "Unexpected first packet {}; acking {}; flags={}",
                tcp_header.sequence_number(),
                tcp_header.acknowledgement_number(),
                tcp_header.flags()
            );
            self.tcb.sequence_number = Wrapping(tcp_header.acknowledgement_number());
            self.reply_empty_packet_to_client(client_channel, tcp_header::FLAG_RST);
            self.close();
        }
    }

    fn handle_duplicate_syn(&mut self, client_channel: &mut ClientChannel, ip_packet: &IpPacket) {
        let tcp_header = Self::tcp_header_of_packet(ip_packet);
        let their_sequence_number = tcp_header.sequence_number();
        if self.tcb.state == TcpState::SynSent {
            self.tcb.syn_sequence_number = their_sequence_number;
            self.tcb.acknowledgement_number = Wrapping(their_sequence_number) + Wrapping(1);
        } else if their_sequence_number != self.tcb.syn_sequence_number {
            self.reply_empty_packet_to_client(client_channel, tcp_header::FLAG_RST);
            self.close();
        }
    }

    fn handle_fin(&mut self, _client_channel: &mut ClientChannel) {
        cx_debug!(
            target: TAG,
            self.id,
            "Received a FIN from the client {}",
            self.tcb.numbers()
        );

        self.tcb.fin_received = true;
        if self.client_to_network.is_empty() {
            cx_debug!(
                target: TAG,
                self.id,
                "No pending data, process the FIN immediately"
            );
            self.do_handle_fin();
        }
    }

    fn do_handle_fin(&mut self) {
        self.tcb.acknowledgement_number += Wrapping(1); // received FIN counts for 1 byte

        if self.tcb.state == TcpState::Established {
            self.send_empty_packet_to_client(tcp_header::FLAG_FIN | tcp_header::FLAG_ACK);
            self.tcb.fin_sequence_number = Some(self.tcb.sequence_number.0);
            self.tcb.sequence_number += Wrapping(1);
            self.tcb.state = TcpState::LastAck;
            cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
        } else if self.tcb.state == TcpState::FinWait1 {
            self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
            self.tcb.state = TcpState::Closing;
            cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
        } else if self.tcb.state == TcpState::FinWait2 {
            self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
            self.close();
        } else {
            cx_warn!(
                target: TAG,
                self.id,
                "Received FIN was state was {:?}",
                self.tcb.state
            );
        }
    }

    fn handle_fin_ack(&mut self) {
        if self.tcb.state == TcpState::LastAck || self.tcb.state == TcpState::Closing {
            self.close();
        } else if self.tcb.state == TcpState::FinWait1 {
            self.tcb.state = TcpState::FinWait2;
            cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
        } else if self.tcb.state != TcpState::FinWait2 {
            cx_warn!(
                target: TAG,
                self.id,
                "Received FIN ACK while state was {:?}",
                self.tcb.state
            );
        }
    }

    fn handle_ack(&mut self, _client_channel: &mut ClientChannel, ip_packet: &IpPacket) {
        cx_debug!(target: TAG, self.id, "handle_ack()");
        if self.tcb.state == TcpState::SynReceived {
            self.tcb.state = TcpState::Established;
            cx_debug!(target: TAG, self.id, "State = {:?}", self.tcb.state);
            return;
        }

        if log_enabled!(target: TAG, Level::Trace) {
            cx_trace!(
                target: TAG,
                self.id,
                "{}",
                binary::build_packet_string(ip_packet.raw())
            );
        }

        let payload = match ip_packet.payload() {
            Some(p) if !p.is_empty() => p,
            _ => return,
        };

        // Logging adicional
        let buffer_remaining = self.client_to_network.remaining();
        let buffer_total = self.client_to_network.capacity();
        let buffer_used = buffer_total - buffer_remaining;
        let advertised = self.advertised_window();
    
        if buffer_remaining < payload.len() {
            cx_warn!(
                target: TAG,
                self.id,
                "BUFFER FULL: remaining={}, payload={}, advertised_window={}, used={}/{}",
                buffer_remaining, payload.len(), advertised, buffer_used, buffer_total
            );
        }

        if self.client_to_network.remaining() < payload.len() {
            cx_warn!(target: TAG, self.id, "Not enough space, dropping packet");
            // Send an ACK with the current window. If the buffer is full, the
            // window will be 0 and the device will stop sending. Without this,
            // the device retransmits forever and every retransmission is
            // ignored (seq mismatch), burning CPU.
            self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
            return;
        }

        self.client_to_network.read_from(payload);
        // Immediate ACK to the device for the bytes just received.
        self.tcb.acknowledgement_number += Wrapping(payload.len() as u32);
        self.send_empty_packet_to_client(tcp_header::FLAG_ACK);
    }

    /// Reply through an explicit `ClientChannel` (used only when the packet
    /// arrives from the device, i.e. when no buffer borrow conflict exists).
    fn reply_empty_packet_to_client(&mut self, client_channel: &mut ClientChannel, flags: u16) {
        let window = self.advertised_window();
        let ip_packet =
            Self::create_empty_response_packet(&self.id, &mut self.network_to_client, &self.tcb, flags, window);
        let _ = client_channel.send_to_client(&ip_packet);
    }

    fn create_empty_response_packet<'a>(
        id: &ConnectionId,
        packetizer: &'a mut Packetizer,
        tcb: &Tcb,
        flags: u16,
        window: u16,
    ) -> IpPacket<'a> {
        Self::update_headers(packetizer, tcb, flags, window);
        cx_debug!(
            target: TAG,
            id,
            "Forging empty response (flags={}) {}",
            flags,
            tcb.numbers()
        );
        if (flags & tcp_header::FLAG_ACK) != 0 {
            cx_debug!(target: TAG, id, "Acking {}", tcb.numbers());
        }
        let ip_packet = packetizer.packetize_empty_payload();
        if log_enabled!(target: TAG, Level::Trace) {
            cx_trace!(
                target: TAG,
                id,
                "{}",
                binary::build_packet_string(ip_packet.raw())
            );
        }
        ip_packet
    }

    fn may_read(&self) -> bool {
        if !self.tcb.state.is_connected() || self.tcb.state.is_closed() {
            return false;
        }
        if self.packet_for_client_length.is_some() {
            return false;
        }
        self.tcb.remaining_client_window() > 0
    }

    /// Advertised TCP receive window: how much space is left in our buffer
    /// for data coming from the device. This provides backpressure — when the
    /// buffer is nearly full, the window shrinks to 0 and the device stops
    /// sending, avoiding the "Not enough space, dropping packet" → retransmit
    /// → "Ignoring packet" loop that burns CPU.
    fn advertised_window(&self) -> u16 {
        scaled_window(self.client_to_network.remaining(), self.tcb.relay_window_scale)
    }

    fn may_write(&self) -> bool {
        !self.client_to_network.is_empty()
    }
}

impl Connection for TcpConnection {
    fn id(&self) -> &ConnectionId {
        &self.id
    }

    fn send_to_network(&mut self, client_channel: &mut ClientChannel, ip_packet: &IpPacket) {
        self.handle_packet(client_channel, ip_packet);
    }

    fn close(&mut self) {
        cx_info!(target: TAG, self.id, "Close");
        self.closed = true;
    }

    fn is_expired(&self) -> bool {
        false
    }

    fn is_closed(&self) -> bool {
        self.closed
    }

    fn poll(&mut self) -> io::Result<()> {
        self.poll_self()
    }
}

#[cfg(test)]
mod tests {
    use super::build_socks5_connect_request;
    use super::{CLIENT_TO_NETWORK_CAPACITY, Tcb, TcpConnection, scaled_window, window_scale_for};
    use super::{DEFAULT_MAX_PAYLOAD_LENGTH, max_payload_length_for};
    use super::{connect_nonblocking, connect_status, recv_buffer_size};
    use crate::relay::ip_packet::IpPacket;
    use crate::relay::transport_header::TransportHeader;
    use socket2::{Domain, Socket, Type};
    use std::io;
    use std::net::{TcpListener, TcpStream};
    use std::num::Wrapping;
    use std::time::{Duration, Instant};

    /// Poll `connect_status()` until the connect completes, fails, or 5 seconds pass.
    fn wait_for_connect(stream: &TcpStream) -> io::Result<bool> {
        let deadline = Instant::now() + Duration::from_secs(5);
        while !connect_status(stream)? {
            if Instant::now() >= deadline {
                return Ok(false);
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        Ok(true)
    }

    #[test]
    fn small_receive_buffer_for_local_servers_only() {
        let local = [
            "127.0.0.1:1",
            "192.168.1.101:38830",
            "10.0.0.5:1",
            "172.16.0.1:1",
            "169.254.1.1:1",
            "[::1]:1",
            "[fd00::1]:1",
            "[fe80::1]:1",
        ];
        for address in local {
            assert_eq!(256 * 1024, recv_buffer_size(&address.parse().unwrap()), "{}", address);
        }
        for address in ["8.8.8.8:443", "57.144.245.141:443", "[2001:4860:4860::8888]:443"] {
            assert_eq!(1024 * 1024, recv_buffer_size(&address.parse().unwrap()), "{}", address);
        }
    }

    #[test]
    fn nonblocking_connect_completes() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let stream = connect_nonblocking(&listener.local_addr().unwrap()).unwrap();
        assert!(wait_for_connect(&stream).unwrap());
    }

    #[test]
    fn nonblocking_connect_reports_refusal() {
        let address = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap();
        // the listener is dropped: nothing accepts on this port any more
        let result = connect_nonblocking(&address).and_then(|stream| wait_for_connect(&stream));
        assert!(result.is_err(), "expected a refused connection, got {:?}", result);
    }

    #[test]
    fn nonblocking_connect_does_not_wait_for_the_server() {
        // A socket bound without listening: macOS drops SYNs to it without a reset, so a blocking
        // connect would wait for the OS connect timeout (Linux refuses the connection instead).
        let silent = Socket::new(Domain::IPV4, Type::STREAM, None).unwrap();
        silent.bind(&SocketAddr::from(([127, 0, 0, 1], 0)).into()).unwrap();
        let address = silent.local_addr().unwrap().as_socket().unwrap();
        let start = Instant::now();
        let _ = connect_nonblocking(&address);
        assert!(
            start.elapsed() < Duration::from_millis(500),
            "connect blocked for {:?}",
            start.elapsed()
        );
    }

    /// TCP header of a Linux SYN: MSS, SACK permitted, timestamps, NOP, window scale 7.
    fn linux_syn_tcp_header() -> Vec<u8> {
        let mut tcp = vec![
            0x9a, 0x48, 0x97, 0xae, // source port 39496, destination port 38830
            0x12, 0x34, 0x56, 0x78, // sequence number
            0, 0, 0, 0, // acknowledgement number
            0xa0, 0x02, // data offset 10 words (40 bytes), flags SYN
            0xff, 0xff, // window
            0, 0, 0, 0, // checksum, urgent pointer
        ];
        tcp.extend_from_slice(&[2, 4, 0x3f, 0xd8, 4, 2, 8, 10, 0, 0, 0, 1, 0, 0, 0, 0, 1, 3, 3, 7]);
        tcp
    }

    fn ipv4_syn() -> Vec<u8> {
        let tcp = linux_syn_tcp_header();
        let mut raw = vec![0x45, 0, 0, 0, 0, 0, 0x40, 0, 64, 6, 0, 0, 10, 0, 0, 2, 192, 168, 1, 101];
        let total_length = (raw.len() + tcp.len()) as u16;
        raw[2..4].copy_from_slice(&total_length.to_be_bytes());
        raw.extend_from_slice(&tcp);
        raw
    }

    fn ipv6_syn() -> Vec<u8> {
        let tcp = linux_syn_tcp_header();
        let mut raw = vec![0x60, 0, 0, 0];
        raw.extend_from_slice(&(tcp.len() as u16).to_be_bytes());
        raw.extend_from_slice(&[6, 64]); // next header TCP, hop limit
        raw.extend_from_slice(&[0xfd, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]); // source
        raw.extend_from_slice(&[0xfd, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]); // destination
        raw.extend_from_slice(&tcp);
        raw
    }

    /// One's complement sum (RFC 1071), continuing from `sum`.
    fn checksum(data: &[u8], mut sum: u32) -> u32 {
        for chunk in data.chunks(2) {
            sum += (u32::from(chunk[0]) << 8) | u32::from(*chunk.get(1).unwrap_or(&0));
        }
        while sum > 0xFFFF {
            sum = (sum & 0xFFFF) + (sum >> 16);
        }
        sum
    }

    fn syn_ack_for(syn: &mut [u8], relay_window_scale: u8) -> Vec<u8> {
        let packet = IpPacket::parse(syn).unwrap();
        let (ip_header, transport_header) = packet.headers();
        let Some(TransportHeader::Tcp(tcp_header)) = transport_header else {
            panic!("Not a TCP packet");
        };
        assert_eq!(Some(7), tcp_header.window_scale());
        let mut packetizer = TcpConnection::create_syn_ack_packetizer(&ip_header, &tcp_header, relay_window_scale);
        packetizer.packetize_empty_payload().raw().to_vec()
    }

    #[test]
    fn syn_ack_carries_window_scale_ipv4() {
        let raw = syn_ack_for(&mut ipv4_syn(), 6);
        assert_eq!(44, raw.len());
        assert_eq!(44, u16::from_be_bytes([raw[2], raw[3]]));
        assert_eq!(0xFFFF, checksum(&raw[..20], 0), "IPv4 header checksum");
        let tcp = &raw[20..];
        assert_eq!(&tcp[..4], &[0x97, 0xae, 0x9a, 0x48], "ports must be swapped");
        assert_eq!(6, tcp[12] >> 4, "data offset");
        assert_eq!(&tcp[20..24], &[1, 3, 3, 6]);
        let mut pseudo = raw[12..20].to_vec();
        pseudo.extend_from_slice(&[0, 6, 0, tcp.len() as u8]);
        assert_eq!(0xFFFF, checksum(tcp, checksum(&pseudo, 0)), "TCP checksum");
    }

    #[test]
    fn syn_ack_carries_window_scale_ipv6() {
        let raw = syn_ack_for(&mut ipv6_syn(), 6);
        assert_eq!(64, raw.len());
        assert_eq!(24, u16::from_be_bytes([raw[4], raw[5]]), "payload length");
        let tcp = &raw[40..];
        assert_eq!(6, tcp[12] >> 4, "data offset");
        assert_eq!(&tcp[20..24], &[1, 3, 3, 6]);
        let mut pseudo = raw[8..40].to_vec();
        pseudo.extend_from_slice(&[0, 0, 0, tcp.len() as u8, 0, 0, 0, 6]);
        assert_eq!(0xFFFF, checksum(tcp, checksum(&pseudo, 0)), "TCP checksum");
    }

    #[test]
    fn reset_for_syn_acknowledges_the_syn() {
        let syn = ipv6_syn();
        let mut packet_raw = syn.clone();
        let raw = TcpConnection::reset_for_syn(&IpPacket::parse(&mut packet_raw).unwrap()).unwrap();
        assert_eq!(60, raw.len());
        assert_eq!(20, u16::from_be_bytes([raw[4], raw[5]]), "payload length");
        assert_eq!(&raw[8..24], &syn[24..40], "source must be the original destination");
        assert_eq!(&raw[24..40], &syn[8..24], "destination must be the original source");
        let tcp = &raw[40..];
        assert_eq!(&tcp[..4], &[0x97, 0xae, 0x9a, 0x48], "ports must be swapped");
        assert_eq!(&tcp[4..8], &[0, 0, 0, 0], "sequence number");
        assert_eq!(&tcp[8..12], &[0x12, 0x34, 0x56, 0x79], "must acknowledge the SYN");
        assert_eq!(5, tcp[12] >> 4, "data offset");
        assert_eq!(0x14, tcp[13], "flags RST|ACK");
        let mut pseudo = raw[8..40].to_vec();
        pseudo.extend_from_slice(&[0, 0, 0, tcp.len() as u8, 0, 0, 0, 6]);
        assert_eq!(0xFFFF, checksum(tcp, checksum(&pseudo, 0)), "TCP checksum");
    }

    #[test]
    fn reset_for_syn_ignores_other_packets() {
        let mut ack = ipv4_syn();
        ack[33] = 0x10; // flags ACK
        assert!(TcpConnection::reset_for_syn(&IpPacket::parse(&mut ack).unwrap()).is_none());
    }

    #[test]
    fn segments_follow_the_device_mss() {
        assert_eq!(16344, max_payload_length_for(Some(16344)));
        assert_eq!(1220, max_payload_length_for(Some(1220)));
    }

    #[test]
    fn segments_without_mss_keep_the_default() {
        assert_eq!(DEFAULT_MAX_PAYLOAD_LENGTH, max_payload_length_for(None));
        assert_eq!(DEFAULT_MAX_PAYLOAD_LENGTH, max_payload_length_for(Some(0)));
    }

    #[test]
    fn segments_fit_a_16_bit_packet_length() {
        let payload = max_payload_length_for(Some(u16::MAX));
        // largest headers: IPv6 (40 bytes) and TCP without options (20 bytes)
        assert!(u32::from(payload) + 60 <= u32::from(u16::MAX));
    }

    #[test]
    fn window_scale_covers_buffer_capacity() {
        assert_eq!(0, window_scale_for(65535));
        assert_eq!(1, window_scale_for(65536));
        assert_eq!(6, window_scale_for(CLIENT_TO_NETWORK_CAPACITY));
        assert_eq!(14, window_scale_for(usize::MAX));
    }

    #[test]
    fn scaled_window_never_overstates_free_space() {
        assert_eq!(65535, scaled_window(CLIENT_TO_NETWORK_CAPACITY, 0));
        assert_eq!(32768, scaled_window(CLIENT_TO_NETWORK_CAPACITY, 6));
        assert_eq!(0, scaled_window(63, 6));
        assert_eq!(1, scaled_window(127, 6));
    }

    #[test]
    fn remaining_client_window_beyond_64k() {
        let mut tcb = Tcb::new();
        tcb.their_acknowledgement_number = 1000;
        tcb.sequence_number = Wrapping(1000 + 4096);
        // window field 32767 with a client shift of 7: about 4 MiB
        tcb.client_window = 0x7fff << 7;
        assert_eq!((0x7fff << 7) - 4096, tcb.remaining_client_window());
    }
    use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr};

    #[test]
    fn socks5_request_ipv4_layout() {
        let dest: SocketAddr = (Ipv4Addr::new(8, 8, 8, 8), 443).into();
        let req = build_socks5_connect_request(&dest);
        assert_eq!(req, vec![0x05, 0x01, 0x00, 0x01, 8, 8, 8, 8, 0x01, 0xBB]);
    }

    #[test]
    fn socks5_request_ipv6_layout() {
        let addr = Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1);
        let dest: SocketAddr = (addr, 443).into();
        let req = build_socks5_connect_request(&dest);
        let mut expected = vec![0x05, 0x01, 0x00, 0x04];
        expected.extend_from_slice(&addr.octets());
        expected.extend_from_slice(&[0x01, 0xBB]);
        assert_eq!(req, expected);
    }

    #[test]
    fn socks5_request_ipv4_length() {
        let dest: SocketAddr = (Ipv4Addr::new(1, 1, 1, 1), 53).into();
        assert_eq!(build_socks5_connect_request(&dest).len(), 10);
    }

    #[test]
    fn socks5_request_ipv6_length() {
        let dest: SocketAddr = (Ipv6Addr::LOCALHOST, 53).into();
        assert_eq!(build_socks5_connect_request(&dest).len(), 22);
    }

    #[test]
    fn socks5_request_port_is_big_endian() {
        let dest: SocketAddr = (Ipv4Addr::new(1, 2, 3, 4), 0x1234).into();
        let req = build_socks5_connect_request(&dest);
        assert_eq!(&req[req.len() - 2..], &[0x12, 0x34]);
    }

    #[test]
    fn socks5_request_ipv6_port_is_big_endian() {
        let dest: SocketAddr = (Ipv6Addr::LOCALHOST, 0xABCD).into();
        let req = build_socks5_connect_request(&dest);
        assert_eq!(&req[req.len() - 2..], &[0xAB, 0xCD]);
    }

    #[test]
    fn socks5_request_rejects_nothing() {
        let v4: SocketAddr = (Ipv4Addr::UNSPECIFIED, 1).into();
        let v6: SocketAddr = (Ipv6Addr::UNSPECIFIED, 1).into();
        assert_eq!(build_socks5_connect_request(&v4)[3], 0x01);
        assert_eq!(build_socks5_connect_request(&v6)[3], 0x04);
    }
}
