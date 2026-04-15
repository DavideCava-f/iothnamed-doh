/*
 * iothnamed: a domain name server/forwarder/proxy for the ioth
 * Copyright 2021 Renzo Davoli - Federico De Marchi
 *     Virtualsquare & University of Bologna
 *
 * mainloop.c: main event loop
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <poll.h>

#include <sys/epoll.h>
#include <sys/socket.h>

#include <netinet/in.h>
#include <arpa/inet.h>

#include <ioth.h>
#include <iothconf.h>
#include <iothdns.h>

#include <utils.h>
#include <arpainetx.h>
#include <tcpq.h>
#include <now.h>
#include <dnsreqq.h>
#include <auth.h>
#include <cache.h>
#include <dnsheader_flags.h>
#include <process_dns_req.h>
#include <fdtimeout.h>

#include <wolfssl/options.h>
#include <wolfssl/ssl.h>
#include <wolfssl/test.h>

#define USE_DOH 1
#define HTTPS_PORT 443
#define DNS_UDP_PORT 53
#define ckretval(retval, X) do { \
	if (retval < 0) { \
		printlog(LOG_ERR, X ": %s", strerror(errno)); \
		return -1; \
	} \
} while (0)

enum client_type {
    TCP_CLIENT,
    DOH_CLIENT
};

static struct ioth *rstack; // req stack
static struct ioth *fstack; // fwd stack
static struct in6_addr *fwdaddr;
static int fwdaddr_count;
static int fwdaddr_rr; // round robin scan index

#define CMSG_PKTINFO_SIZE CMSG_SPACE(sizeof(struct in6_pktinfo))
static int epollfd;
/* fd names: xyfd where:
	 x == 'u' -> UDP
	 x == 't' -> TCP
	 y == 'r' -> client requests
	 y == 'f' -> forwarding
	 y == 'l' -> listening (tcp) */
static int urfd = -1;  // udp requests fd
static int uffd = -1;  // udp forward fd
static int tlfd = -1;  // tcp listen fd
static int tffd[IOTHDNS_MAXNS] = {-1, -1, -1};  // tcp forward fd

static int dohfd = -1; //TODO rename dohffd
static WOLFSSL *dohssl;
static WOLFSSL_CTX *doh_ctx;

static int dohlfd = -1; //listening for https requests
static WOLFSSL_CTX *doh_server_ctx;

static int tcp_listen_backlog = 5;

// DOH
struct dohdata {
    enum client_type ctype;
    WOLFSSL *ssl;
    int fd;

    char hdr_buf[1024];   
    int hdr_pos;          
    int hdr_done;         

    uint8_t *buf;         
    size_t len;  
    size_t pos; 
};

/* DOH forward function prototypes */
int doh_wrap_dns_req(char *http_req, size_t http_req_max_len, char *buf, size_t len, const char *remote_server);
void close_doh_connection(struct dohdata *dd, char *message, int loginfo);
int doh_ssl_recv_cb(WOLFSSL *ssl, char *buf, int sz, void *ctx);
int doh_ssl_send_cb(WOLFSSL *ssl, char *buf, int sz, void *ctx);
void init_ssl_ctx(); 
static int wake_doh(void);
static long parse_content_length(const char *headers);
ssize_t tcp_doh_recv(struct dohdata *dd);
ssize_t tcp_doh_send(WOLFSSL *ssl, void *buf, size_t len, const char *hostname);
void process_dohfd(uint32_t events);

/* DOH listening function prototypes */
void process_dohlfd(void); // listen for https requests and open ssl connection if needed
void process_dohrfd(void* data, uint32_t events); 
void init_ssl_server_ctx(void);

static void tcp_timeout_cb(int fd) {
	ioth_shutdown(fd, SHUT_RDWR);
}

void cleaning(time_t now) {
	dnsreq_clean(now, NULL, NULL);
	cache_clean(now);
	fd_timeout_clean(now, tcp_timeout_cb);
}

/* UDP forwarder */

/* POLLIN event from a UDP client */
void process_urfd(void) {
	char buf[IOTHDNS_UDP_MAXBUF];
	struct sockaddr_in6 sock;

	uint8_t ctlbuf[CMSG_PKTINFO_SIZE];
	struct msghdr msghdr = {
		.msg_name = &sock,
		.msg_namelen = sizeof(sock),
		.msg_iov = &((struct iovec) {buf, IOTHDNS_UDP_MAXBUF}),
		.msg_iovlen = 1,
		.msg_control = ctlbuf,
		.msg_controllen = sizeof(ctlbuf),
	};
	struct iothdns_header h;
	char qnamebuf[IOTHDNS_MAXNAME];
	size_t len = ioth_recvmsg(urfd, &msghdr, 0);
	struct iothdns_pkt *pkt = iothdns_get_header(&h, buf, len, qnamebuf);
	if (pkt) {
		struct iothdns_pkt *rpkt = process_dns_req(&h, &sock.sin6_addr);
		if (rpkt != NULL) {
			struct iovec rpktbuf = iothdns_getbuf(rpkt);
			if (rpktbuf.iov_len > IOTHDNS_UDP_MAXBUF) {
				struct iothdns_header th = h;
				th.flags = FLAGS_TRUNC(th.flags);
				struct iothdns_pkt *tpkt = iothdns_put_header(&th);
				*msghdr.msg_iov = iothdns_getbuf(tpkt);
				ioth_sendmsg(urfd, &msghdr, 0);
				iothdns_free(tpkt);
			} else {
				*msghdr.msg_iov = rpktbuf;
				ioth_sendmsg(urfd, &msghdr, 0);
			}
			iothdns_free(rpkt);
		} else if (fwdaddr_count > 0){
			int serverid = dnsreq_put(h.id, h.qname, h.qtype, urfd, &msghdr);
			iothdns_rewrite_header(pkt, serverid, h.flags);
#if FWD_PKT_DUMP
			printf("%d %d\n",h.id,serverid);
			printf("========>>>>>>>>>>>>\n");
			packetdump(stdout, buf, len);
#endif
			struct sockaddr_in6 sfwd = {
				.sin6_family = AF_INET6,
				.sin6_addr = fwdaddr[fwdaddr_rr],
				.sin6_port = htons(DNS_UDP_PORT)};
            
            printf("Forwarding request to fstack\n");
            if(USE_DOH){
                void *bufcopy = malloc(len);
                if (bufcopy) {
                    memcpy(bufcopy, buf, len);
                    tcpq_enqueue(bufcopy, len);
                    wake_doh();
                }
            }else{
			    ioth_sendto(uffd, buf, len, 0, (struct sockaddr *)&sfwd, sizeof(sfwd));
            }
			fwdaddr_rr = (fwdaddr_rr + 1) % fwdaddr_count;
		}
		iothdns_free(pkt);
	}
}

/* POLLIN event from a UDP remote DNS server (reply to a forwarded request)  */
void process_uffd(void) {
	char buf[IOTHDNS_UDP_MAXBUF];
	struct sockaddr_in6 sock;
	struct iothdns_header h;
	char qnamebuf[IOTHDNS_MAXNAME];
	size_t len = ioth_recv(uffd, buf, IOTHDNS_UDP_MAXBUF, 0);
#if FWD_PKT_DUMP
	printf("========<<<<<<<<<<<<\n");
	packetdump(stdout, buf, len);
#endif
	struct iothdns_pkt *pkt = iothdns_get_header(&h, buf, len, qnamebuf);
	if (pkt) {
		int fd;
		uint8_t ctlbuf[CMSG_PKTINFO_SIZE];
		if (auth_isactive(AUTH_CACHE))
			cache_feed(pkt);
		struct iovec pktbuf = iothdns_getbuf(pkt);
		struct msghdr msghdr = {
			.msg_name = &sock,
			.msg_namelen = sizeof(sock),
			.msg_iov = &pktbuf,
			.msg_iovlen = 1,
			.msg_control = ctlbuf,
			.msg_controllen = sizeof(ctlbuf),
		};
		int clientid = dnsreq_get(h.id, h.qname, h.qtype, &fd, &msghdr);
#if FWD_PKT_DUMP
		printf("%d %d\n",h.id,clientid);
#endif
		if  (clientid != -1 && fd == urfd) {
			iothdns_rewrite_header(pkt, clientid, h.flags);
			ioth_sendmsg(urfd, &msghdr, 0);
		}
		iothdns_free(pkt);
	}
}

/* TCP forwarder */

/* add the TCP header (length) */
static ssize_t dns_tcp_send(int fd, void *buf, size_t len, int flags) {
  uint8_t hlen[2];
  struct iovec iov[2] = {{hlen, 2},{buf, len}};
  struct msghdr msg = {.msg_iov = iov, .msg_iovlen = 2};
  hlen[0] = len >> 8;
  hlen[1] = len;
#if FWD_PKT_DUMP
	printf("sendmsg %d\n", fd);
#endif
  return ioth_sendmsg(fd, &msg, flags);
}


/* * Mimics dns_tcp_send but for DoH.
 * Wraps the DNS packet in HTTP and sends it over the SSL connection.
 * * @param ssl: The WolfSSL session
 * @param buf: The raw DNS packet (without TCP length header)
 * @param len: Length of the DNS packet
 * @param hostname: The Host header value (e.g., "dns.google")
 * @return: Bytes written or -1 on error
 */

struct tcpdata {
    enum client_type ctype;
	int fd;
	uint16_t len;  /* len of the current request */
	uint16_t pos;  /* offset for reading the remaining part of the request */
	/*                the request is complete when pos == len */
	uint8_t *buf;  /* syn-allocated buffer, NULL if no packet is currently processed */
};

/* reconstruct DNS requests on TCP stream */
ssize_t dns_tcp_recv(struct tcpdata *td) {
	ssize_t rlen;
	if (td->buf == NULL) { /* new packet */
		uint8_t hlen[2] = {0, 0};
		if ((rlen = recv(td->fd, hlen, 2, 0)) <= 0)
			return rlen;
		td->len = (hlen[0] << 8) + hlen[1];
		td->pos = 0;
		td->buf = malloc(td->len);
	} else {
		/* try to get the remaining part of the incoming request */
		if ((rlen = recv(td->fd, td->buf + td->pos, td->len - td->pos, 0)) <= 0)
			return rlen;
		td->pos += rlen;
	}
	return rlen;
}



/* POLLIN event on a TCP listener -> accept */
void process_tlfd(void) {
	struct sockaddr_in6 sock;
	socklen_t socklen = sizeof(sock);
	int connfd = ioth_accept(tlfd, (struct sockaddr *)&sock, &socklen);
	if (connfd >= 0) {
		if (authck(AUTH_ACCEPT, &sock.sin6_addr) == 0)
			close(connfd);
		else {
			struct tcpdata *td = calloc(1, sizeof(*td));
			td->fd = connfd;
            td->ctype = TCP_CLIENT;
			fd_timeout_add(now(), connfd);
			epoll_ctl(epollfd, EPOLL_CTL_ADD, connfd, &((struct epoll_event){.events=POLLIN, .data.ptr = td}));
		}
	}
}


/* There is data in tcpq to the forwarding server */
static int wake_tcp(void) {
	/* if the connection to the server is not active, do a asynch connect */
	struct epoll_event ev = {
		.events=POLLIN | POLLOUT,
		.data.ptr = &tffd[fwdaddr_rr]
	};
	if (tffd[fwdaddr_rr] < 0) {
		int retval;
		struct sockaddr_in6 sfwd = {.sin6_family = AF_INET6, .sin6_addr = fwdaddr[fwdaddr_rr], .sin6_port = htons(DNS_UDP_PORT)};
		retval = tffd[fwdaddr_rr] = ioth_msocket(fstack, AF_INET6, SOCK_STREAM | SOCK_NONBLOCK, 0);
		ckretval(retval, "tcp forward fd msocket");
		retval = ioth_connect(tffd[fwdaddr_rr], (struct sockaddr *)&sfwd, sizeof(sfwd));
		if (retval < 0 && errno != EINPROGRESS)
			ckretval(retval, "tcp forward fd connect");
		epoll_ctl(epollfd, EPOLL_CTL_ADD, tffd[fwdaddr_rr], &ev);
	} else
		epoll_ctl(epollfd, EPOLL_CTL_MOD, tffd[fwdaddr_rr], &ev);
	fwdaddr_rr = (fwdaddr_rr + 1) % fwdaddr_count;
	return 0;
}

/* POLLIN event from a TCP client */
void process_trfd(void *data) {
	struct tcpdata *td = data;
	ssize_t rlen = dns_tcp_recv(td);
	if (rlen <= 0) {
		/* the client prematurely closed the stream */
		/* delete the epoll entry */
		epoll_ctl(epollfd, EPOLL_CTL_DEL, td->fd, NULL);
		/* drop all the pending requests */
		dnsreq_delfd(td->fd, NULL, NULL);
		fd_timeout_del(td->fd);
		close(td->fd);
		if (td->buf) free(td->buf);
		free(td);
	} else if (td->pos == td->len) {
		/* the incoming request is complete, it can be processed */
		struct iothdns_header h;
		char qnamebuf[IOTHDNS_MAXNAME];
		struct iothdns_pkt *pkt = iothdns_get_header(&h, td->buf, td->len, qnamebuf);
		if (pkt) {
			struct sockaddr_in6 sock;
			socklen_t socklen = sizeof(sock);
			fd_timeout_add(now(), td->fd);
			getpeername(td->fd, (struct sockaddr *)&sock, &socklen);
			struct iothdns_pkt *rpkt = process_dns_req(&h, &sock.sin6_addr);
			if (rpkt != NULL) {
				struct iovec rpktbuf = iothdns_getbuf(rpkt);
				dns_tcp_send(td->fd, rpktbuf.iov_base, rpktbuf.iov_len, 0);
				iothdns_free(rpkt);
			} else {
				/* forward the packet */
                printf("client id inserted: %d\n", h.id);
				int serverid = dnsreq_put(h.id, h.qname, h.qtype, td->fd, NULL);
				if (serverid >= 0) {
                    printf("server id: %d\n", serverid);
				    iothdns_rewrite_header(pkt, serverid, h.flags);
                    
#if FWD_PKT_DUMP
					printf("%d %d\n",h.id,serverid);
					printf("========>>>>>>>>>>>>\n");
					packetdump(stdout, td->buf, td->len);
#endif
					/* tcpq_enqueue delays the send to a POLLOUT event on the connection to the remote DNS server */
					/* the queue is shared: it is more a feature than a bug.
					 * A fast server can steal requests intentionally for another server */
					tcpq_enqueue(td->buf, td->len);
                    if(USE_DOH) {
                        wake_doh();
                    }else{
                        wake_tcp();
                    }
					/* this avoids to free the buf, enqueued for the delayed sending */
					td->buf = NULL;
				}
			}
			iothdns_free(pkt);
		}
		if (td->buf) free(td->buf);
		td->len = td->pos = 0;
		td->buf = NULL;
	}
}



/* POLLIN event from a TCP remote DNS server (reply to a forwarded request) */
void process_tffd(int index, uint32_t events) {
    if (events & POLLOUT) {
        /* POLLOUT event, the stream is connected and ready, send the next packet from tcpq */
        int len;
        void *buf = tcpq_dequeue(&len);
        if (buf == NULL) {
            struct epoll_event ev = {
                .events=POLLIN,
                .data.ptr = &tffd[index]
            };
            /* cease to wait for POLLOUT if no more packets in tcpq */
            epoll_ctl(epollfd, EPOLL_CTL_MOD, tffd[index], &ev);
        } else {
            /* send the pkt and free the buf */
            dns_tcp_send(tffd[index], buf, len, 0);
            free(buf);
        }
    }
    if (events & POLLIN) {
        /* POLLIN -> incoming reply */
        static struct tcpdata td[IOTHDNS_MAXNS];
        td[index].fd = tffd[index];
        ssize_t rlen = dns_tcp_recv(&td[index]);
        if (rlen <= 0) {
            tffd[index] = -1;
            close(td[index].fd);
            if (td[index].buf) free(td[index].buf);
        } else if (td[index].pos == td[index].len) {
            struct iothdns_header h;
            char qnamebuf[IOTHDNS_MAXNAME];
            struct iothdns_pkt *pkt = iothdns_get_header(&h, td[index].buf, td[index].len, qnamebuf);
            if (pkt) {
                int fd;
                if (auth_isactive(AUTH_CACHE))
                    cache_feed(pkt);
                int clientid = dnsreq_get(h.id, h.qname, h.qtype, &fd, NULL);
                if (clientid >= 0) {
                    iothdns_rewrite_header(pkt, clientid, h.flags);
                    struct iovec pktbuf = iothdns_getbuf(pkt);
#if FWD_PKT_DUMP
                    printf("%d %d\n",h.id,clientid);
                    printf("========<<<<<<<<<<<<\n");
                    packetdump(stdout, pktbuf.iov_base, pktbuf.iov_len);
#endif
                    dns_tcp_send(fd, pktbuf.iov_base, pktbuf.iov_len, 0);
                }
                iothdns_free(pkt);
                td[index].len = td[index].pos = 0;
                free(td[index].buf);
                td[index].buf = NULL;
            }
        }
    }
}

int doh_wrap_dns_req(char* http_req, size_t http_req_max_len, char* buf, size_t len, const char* remote_server) {
    int header_len = snprintf(http_req, http_req_max_len,
            "POST /dns-query HTTP/1.1\r\n"
            "Host: %s\r\n"
            "Content-Type: application/dns-message\r\n"
            "Accept: application/dns-message\r\n"
            "Content-Length: %zu\r\n"
            "Connection: keep-alive\r\n" // Or "keep-alive" if you plan to reuse the WolfSSL session
            "\r\n",
            remote_server, len
            );

    if (header_len < 0 || (size_t)header_len >= http_req_max_len) {
        printf("https-wrap: invalid header len\n");
        return -1; 
    }
    if ((size_t)header_len + len > http_req_max_len) {
        printf("https-wrap: invalid https packet len\n");
        return -1; 
    }
    
    //copy dns request into https body
    memcpy(http_req + header_len, buf, len);
    return header_len + len;
}

void close_doh_connection(struct dohdata* dd, char* message, int loginfo){
    printlog(loginfo, message);
    epoll_ctl(epollfd, EPOLL_CTL_DEL, dohfd, NULL);
    if (dohssl) {
        wolfSSL_free(dohssl);
        dohssl = NULL;
    }
    ioth_close(dohfd);
    dohfd = -1;
    if (dd->buf) free(dd->buf);
    memset(dd, 0, sizeof(*dd));
}




int doh_ssl_recv_cb(WOLFSSL* ssl, char* buf, int sz, void* ctx) {
    int fd = (int)(intptr_t)ctx;
    int ret = ioth_recv(fd, buf, sz, MSG_DONTWAIT);
    if (ret < 0) {
        int err = errno;
        if (err == EAGAIN || err == EWOULDBLOCK)
            return WOLFSSL_CBIO_ERR_WANT_READ;

        return WOLFSSL_CBIO_ERR_GENERAL;
    }
    if (ret == 0)
        return WOLFSSL_CBIO_ERR_CONN_CLOSE;
    return ret;
}

int doh_ssl_send_cb(WOLFSSL* ssl, char* buf, int sz, void* ctx) {
    int fd = (int)(intptr_t)ctx;
    int ret = ioth_send(fd, buf, sz, 0);
    if (ret < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK)
            return WOLFSSL_CBIO_ERR_WANT_WRITE;
        return WOLFSSL_CBIO_ERR_GENERAL;
    }
    return ret;
}
void init_ssl_ctx() {
    wolfSSL_Init();
    doh_ctx = wolfSSL_CTX_new(wolfTLSv1_3_client_method());

    if(!doh_ctx) {
        printlog(LOG_ERR,"Failed to initialize ssl context");
        //exit(0);
    }
    // bind calback functions
    wolfSSL_SetIORecv(doh_ctx, doh_ssl_recv_cb);
    wolfSSL_SetIOSend(doh_ctx, doh_ssl_send_cb);
    printlog(LOG_INFO,"SSL context correctly initialized");
}


static int wake_doh(void) {
	/* if the connection to the server is not active, do a asynch connect */
	struct epoll_event ev = {
		.events=POLLIN | POLLOUT,
		.data.ptr = &dohfd
	};
	if (dohfd < 0) {
        printlog(LOG_INFO,"doh - connection not active, performing asynch connect");
		int retval;
		struct sockaddr_in6 sfwd = {.sin6_family = AF_INET6, .sin6_addr = fwdaddr[fwdaddr_rr], .sin6_port = htons(HTTPS_PORT)};
		retval = dohfd = ioth_msocket(fstack, AF_INET6, SOCK_STREAM | SOCK_NONBLOCK, 0);
		ckretval(retval, "doh forward fd msocket");
		retval = ioth_connect(dohfd, (struct sockaddr *)&sfwd, sizeof(sfwd));
		if (retval < 0 && errno != EINPROGRESS)
			ckretval(retval, "tcp forward fd connect");
    
        dohssl = wolfSSL_new(doh_ctx);
        wolfSSL_SetIOReadCtx(dohssl, (void*)(intptr_t)dohfd);
        wolfSSL_SetIOWriteCtx(dohssl, (void*)(intptr_t)dohfd);
        int res = wolfSSL_connect(dohssl);
		epoll_ctl(epollfd, EPOLL_CTL_ADD, dohfd, &ev);
	} else {
        printlog(LOG_INFO,"doh - connection active");
		epoll_ctl(epollfd, EPOLL_CTL_MOD, dohfd, &ev);
    }
	fwdaddr_rr = (fwdaddr_rr + 1) % fwdaddr_count;
	return 0;
}

static long parse_content_length(const char *headers) {
    const char *ptr = strcasestr(headers, "Content-Length:");
    if (ptr) {
        ptr += 15; /* Skip "Content-Length:" */
        while (*ptr && isspace((unsigned char)*ptr)) ptr++;
        return strtol(ptr, NULL, 10);
    }
    return -1;
}

ssize_t tcp_doh_recv(struct dohdata *dd) {
    ssize_t rlen;

    if (!dd->hdr_done) {
        printlog(LOG_INFO,"header not done");
        int max_read = sizeof(dd->hdr_buf) - dd->hdr_pos - 1; /* -1 for null terminator */
        if (max_read <= 0) {
            printlog(LOG_ERR,"ERROR: Header too large");
            errno = EMSGSIZE; /* Headers too large */
            return -1;
        }
        rlen = wolfSSL_read(dd->ssl, dd->hdr_buf + dd->hdr_pos, max_read);
        if (rlen <= 0) {
            printlog(LOG_INFO, "rlen = %ld\n", rlen);
            int err  = wolfSSL_get_error(dohssl, rlen);
            if (err == WOLFSSL_ERROR_WANT_READ || err == WOLFSSL_ERROR_WANT_WRITE) {
                printlog(LOG_INFO,"WANT READ");
                errno = EAGAIN;
                return -1;
            }
            char error[256];
            printlog(LOG_ERR, "WolfSSL error %d - %s\n", err, wolfSSL_ERR_error_string(err, error));
            return -1; 
        }

        dd->hdr_pos += rlen;
        dd->hdr_buf[dd->hdr_pos] = '\0'; 

        /* Check for end of headers */
        char *body_start = strstr(dd->hdr_buf, "\r\n\r\n");
        if (body_start) {
            if (strstr(dd->hdr_buf, "HTTP/1.1 200") == NULL && 
                    strstr(dd->hdr_buf, "HTTP/1.0 200") == NULL) {

                printlog(LOG_ERR,"ERROR: DoH Server returned error (Not 200 OK):\n%.*s\n", 
                        (int)(strchr(dd->hdr_buf, '\r') - dd->hdr_buf), dd->hdr_buf);

                errno = EPROTO; 
                return -1;
            }
            long content_len = parse_content_length(dd->hdr_buf);
            
            if (content_len < 0) {
                printlog(LOG_ERR,"ERROR: valid https, missing Content-Length\n");
                errno = EPROTO; 
                return -1;
            }

            dd->len = (size_t)content_len;
            dd->buf = malloc(dd->len);
            if (!dd->buf) {
                printlog(LOG_ERR,"ERROR: cannot allocate message buf");
                errno = ENOMEM;
                return -1;
            }
            dd->pos = 0;
            dd->hdr_done = 1;

            // Handle Body Over-read
            int header_size = (body_start - dd->hdr_buf) + 4; /* +4 for \r\n\r\n */
            int body_bytes_read = dd->hdr_pos - header_size;

            if (body_bytes_read > 0) {
                if ((size_t)body_bytes_read > dd->len) {
                     body_bytes_read = dd->len;
                }
                memcpy(dd->buf, body_start + 4, body_bytes_read);
                dd->pos += body_bytes_read;
            }
            
            if (dd->pos == dd->len) {
                printlog(LOG_INFO,"packet done");
                return rlen; 
            }
        } else {
             return rlen;
        }
    }

    // Read DNS Body 
    if (dd->hdr_done && dd->pos < dd->len) {
        printlog(LOG_INFO,"reading body");
        rlen = wolfSSL_read(dd->ssl, (char *)dd->buf + dd->pos, dd->len - dd->pos);
        
        if (rlen <= 0) {
            return rlen;
        }
        
        dd->pos += rlen;
        return rlen;
    }
    return 0;
}

ssize_t tcp_doh_send(WOLFSSL *ssl, void *buf, size_t len, const char *hostname) {
    printlog(LOG_INFO,"forwarding dns request to doh server");
    size_t overhead = 512;
    size_t req_max_len = len + overhead;
    
    char *req_buf = malloc(req_max_len);
    if (!req_buf) {
        errno = ENOMEM;
        return -1;
    }
    int http_len = doh_wrap_dns_req(req_buf, req_max_len, buf, len, hostname);
    if (http_len < 0) {
        free(req_buf);
        errno = EINVAL; 
        return -1;
    }
    int ret = wolfSSL_write(ssl, req_buf, http_len);
    free(req_buf);

    if (ret <= 0) {
        int err = wolfSSL_get_error(ssl, ret);
        if (err == WOLFSSL_ERROR_WANT_WRITE || err == WOLFSSL_ERROR_WANT_READ) {
            errno = EAGAIN; /* Signal to mainloop to poll again */
        } else {
            errno = EIO; /* Generic IO error */
        }
        return -1;
    }

    printlog(LOG_INFO,"forwarding dns request to doh server successfull");
    return ret;
}


void process_dohfd(uint32_t events) {
    if (!wolfSSL_is_init_finished(dohssl)) {
        int ret = wolfSSL_connect(dohssl);
        if (ret < 0) {
            int err = wolfSSL_get_error(dohssl, ret);
            if (err == WOLFSSL_ERROR_WANT_READ) {
                /* Handshake needs to read: Ensure we listen for POLLIN */
                struct epoll_event ev = { .events = POLLIN, .data.ptr = &dohfd };
                epoll_ctl(epollfd, EPOLL_CTL_MOD, dohfd, &ev);
                return; 
            }
            if (err == WOLFSSL_ERROR_WANT_WRITE) {
                /* Handshake needs to write: Ensure we listen for POLLOUT */
                struct epoll_event ev = { .events = POLLIN | POLLOUT, .data.ptr = &dohfd };
                epoll_ctl(epollfd, EPOLL_CTL_MOD, dohfd, &ev);
                return;
            }
            // Handshake failed with an error
            fprintf(stderr, "TLS handshake failed\n");
            epoll_ctl(epollfd, EPOLL_CTL_DEL, dohfd, NULL);
            wolfSSL_free(dohssl);
            ioth_close(dohfd);
            dohssl = NULL;
            dohfd = -1;
            return;
        }
        /* Handshake just completed. Don't process POLLIN yet —
           there's no DNS response pending, only send queued data. */
        printf("TLS handshake complete\n");
        events &= ~POLLIN;
    }
    if (events & POLLOUT) {
        if (wolfSSL_is_init_finished(dohssl)){
            /* POLLOUT event, the stream is connected and ready, send the next packet from tcpq */
            printf("dohfd POLLOUT, extract next packet from tcpq\n");
            int len;
            void *buf = tcpq_dequeue(&len);
            if (buf == NULL) {
                struct epoll_event ev = {
                    .events=POLLIN,
                    .data.ptr = &dohfd
                };
                /* cease to wait for POLLOUT if no more packets in tcpq */
                printf("cease wating for pollout, tcpq empty\n");
                epoll_ctl(epollfd, EPOLL_CTL_MOD, dohfd, &ev);
            } else {
                /* send the pkt and free the buf */
                tcp_doh_send(dohssl, buf, len, "dns.google"); //TODO fix with fwdaddr
                /* refresh the dnsreq expiry — the timeout should count from actual send, not enqueue */
                if (len >= 2) {
                    uint16_t serverid = ((uint8_t *)buf)[0] << 8 | ((uint8_t *)buf)[1];
                    dnsreq_refresh_expire(serverid);
                }
                free(buf);
            }
        }

    }
    if (events & POLLIN) {
        /* POLLIN -> incoming reply */
        printf("dohfd POLLIN, reply from remote server\n");
		static struct dohdata dd;
		dd.fd = dohfd;
        dd.ssl = dohssl;
        for(;;){
            ssize_t rlen = tcp_doh_recv(&dd);
            if (rlen < 0) {
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                    printf("partial read\n");
                    break;
                } 
                close_doh_connection(&dd, "Fatal Error or Connection Close", LOG_ERR);
                return;
            } 
            if(rlen == 0) {
                close_doh_connection(&dd, "Connection Closed by Peer", LOG_INFO);
                return;
            }
            if (dd.pos == dd.len) {
                struct iothdns_header h;
                char qnamebuf[IOTHDNS_MAXNAME];
                struct iothdns_pkt *pkt = iothdns_get_header(&h, dd.buf, dd.len, qnamebuf);
                if (pkt) {
                    printlog(LOG_INFO,"iothdns_pkt not null");
                    int fd;
                    uint8_t ctlbuf[CMSG_PKTINFO_SIZE];
                    struct sockaddr_in6 sock;
                    struct iovec pktbuf = iothdns_getbuf(pkt);
                    struct msghdr msghdr = {
                        .msg_name = &sock,
                        .msg_namelen = sizeof(sock),
                        .msg_iov = &pktbuf,
                        .msg_iovlen = 1,
                        .msg_control = ctlbuf,
                        .msg_controllen = sizeof(ctlbuf),
                    };
                    int clientid = dnsreq_get(h.id, h.qname, h.qtype, &fd, &msghdr);
                    if (clientid >= 0) {
                        iothdns_rewrite_header(pkt, clientid, h.flags);
                        pktbuf = iothdns_getbuf(pkt);

                        #if FWD_PKT_DUMP 
                        printf("%d %d\n",h.id,clientid);
                        printf("========<<<<<<<<<<<<\n");
                        packetdump(stdout, pktbuf.iov_base, pktbuf.iov_len);
                        #endif

                        if (fd == urfd) {
                            ioth_sendmsg(urfd, &msghdr, 0);
                        } else {
                            dns_tcp_send(fd, pktbuf.iov_base, pktbuf.iov_len, 0);
                        }
                    }
                }
                iothdns_free(pkt);
                /* Reset dohdata for next response */
                free(dd.buf);
                memset(&dd, 0, sizeof(dd));
                dd.ssl = dohssl;
                dd.fd = dohfd;

                continue;
            }

            break;
        }
    }
}
//ENDDOH

#define NEVENTS 8

int mainloop(struct ioth *_rstack, struct ioth *_fstack, struct in6_addr *_fwdaddr, int _fwdaddr_count) {
    int retval;
    int on = 1;
    rstack = _rstack;
    fstack = _fstack;
    fwdaddr = _fwdaddr;
    fwdaddr_count = _fwdaddr_count;

    struct sockaddr_in6 scli = {.sin6_family = AF_INET6, .sin6_addr = in6addr_any, .sin6_port = htons(DNS_UDP_PORT)};

    init_ssl_ctx(); 
    init_ssl_server_ctx();

    retval = urfd = ioth_msocket(rstack, AF_INET6, SOCK_DGRAM, 0);
    ckretval(retval, "udp request fd msocket");
    retval = ioth_bind(urfd, (struct sockaddr *)&scli, sizeof(scli));
    ckretval(retval, "udp request fd bind");
    ioth_setsockopt(urfd, IPPROTO_IPV6, IPV6_RECVPKTINFO, &on, sizeof(on));

    retval = tlfd = ioth_msocket(rstack, AF_INET6, SOCK_STREAM, 0);
    ckretval(retval, "tcp listening fd msocket");
    retval = ioth_bind(tlfd, (struct sockaddr *)&scli, sizeof(scli));
    ckretval(retval, "tcp listening fd bind");
    retval = ioth_listen(tlfd, tcp_listen_backlog);
    ckretval(retval, "tcp listening fd listen");

    retval = uffd = ioth_msocket(fstack, AF_INET6, SOCK_DGRAM, 0);
    ckretval(retval, "udp forward fd msocket");

    epollfd = epoll_create1(0);
    epoll_ctl(epollfd, EPOLL_CTL_ADD, urfd, &((struct epoll_event){.events=POLLIN, .data.ptr = &urfd}));
    epoll_ctl(epollfd, EPOLL_CTL_ADD, tlfd, &((struct epoll_event){.events=POLLIN, .data.ptr = &tlfd}));
    epoll_ctl(epollfd, EPOLL_CTL_ADD, uffd, &((struct epoll_event){.events=POLLIN, .data.ptr = &uffd}));

    while (alive()) {
        struct epoll_event ev[NEVENTS];
        int nfd = epoll_wait(epollfd, ev, NEVENTS, ms_to_nexttick());
        if (nfd == 0) {
            // new sec: cleaning actions
            time_t newnow = tick();
            cleaning(newnow);
        } else for (int i = 0; i < nfd; i++) {
            struct epoll_event *event = &ev[i];
            if (event->data.ptr == &urfd){
                // UDP client request
                printf("udp request from rstack");
                process_urfd();
            }   
            else if (event->data.ptr == &uffd)     // UDP reply from the server
                process_uffd();
            else if (event->data.ptr == &tlfd)     // TCP new client connection
                process_tlfd();
            else if (event->data.ptr == &tffd[0])     // TCP data from the server 0
                process_tffd(0, event->events);
            else if (event->data.ptr == &tffd[1])     // TCP data from the server 1
                process_tffd(1, event->events);
            else if (event->data.ptr == &tffd[2])     // TCP data from the server 2
                process_tffd(2, event->events);
            else if (event->data.ptr == &dohfd){
                process_dohfd(event->events);
            }
            else {
                enum client_type *ctype = (enum client_type *)event->data.ptr;
                if (*ctype == TCP_CLIENT) {
                    process_trfd(event->data.ptr);
                } else if (*ctype == DOH_CLIENT) {
                    process_dohrfd(event->data.ptr, event->events); 
                }
            }  
        }
    }
    return 0;
}

void mainloop_set_hashttl(int ttl) {
    process_dns_req_set_hashttl(ttl);
}

void mainloop_set_tcp_listen_backlog(int backlog) {
    if (backlog >= 0)
        tcp_listen_backlog = backlog;
}

void mainloop_set_tcp_timeout(int timeout) {
    fd_timeout_set(timeout);
}


/* doh server section */

void process_dohlfd(void) {
	struct sockaddr_in6 sock;
	socklen_t socklen = sizeof(sock);
	int connfd = ioth_accept(tlfd, (struct sockaddr *)&sock, &socklen);
	if (connfd >= 0) {
		if (authck(AUTH_ACCEPT, &sock.sin6_addr) == 0)
			close(connfd);
		else {
			struct dohdata *dd = calloc(1, sizeof(*dd));
			dd->fd = connfd;
            dd->ctype = DOH_CLIENT;

            dd->ssl = wolfSSL_new(doh_server_ctx);
            
            wolfSSL_SetIOReadCtx(dd->ssl, (void*)(intptr_t)connfd);
            wolfSSL_SetIOWriteCtx(dd->ssl, (void*)(intptr_t)connfd);

			fd_timeout_add(now(), connfd);
			epoll_ctl(epollfd, EPOLL_CTL_ADD, connfd, &((struct epoll_event){.events=POLLIN, .data.ptr = dd}));
		}
	}
}

void init_ssl_server_ctx() {
    wolfSSL_Init();
    doh_server_ctx = wolfSSL_CTX_new(wolfTLSv1_3_server_method());

    if(!doh_server_ctx) {
        printlog(LOG_ERR,"Failed to initialize ssl server context");
    }

    if (wolfSSL_CTX_use_certificate_file(doh_server_ctx, "server-cert.pem", SSL_FILETYPE_PEM) != SSL_SUCCESS) {
        printlog(LOG_ERR, "Error loading server-cert.pem");
    }
    
    if (wolfSSL_CTX_use_PrivateKey_file(doh_server_ctx, "server-key.pem", SSL_FILETYPE_PEM) != SSL_SUCCESS) {
        printlog(LOG_ERR, "Error loading server-key.pem");
    }
    // bind calback functions
    wolfSSL_SetIORecv(doh_server_ctx, doh_ssl_recv_cb);
    wolfSSL_SetIOSend(doh_server_ctx, doh_ssl_send_cb);
    printlog(LOG_INFO,"SSL context correctly initialized");
}


void process_dohrfd(void *data, uint32_t events) {
    struct dohdata *dd = (struct dohdata *)data;

    // If WolfSSL hasn't finished the handshake yet...
    if (!wolfSSL_is_init_finished(dd->ssl)) {
        int ret = wolfSSL_accept(dd->ssl); // Note: accept, not connect!
        
        if (ret != WOLFSSL_SUCCESS) {
            int err = wolfSSL_get_error(dd->ssl, ret);
            if (err == WOLFSSL_ERROR_WANT_READ) {
                // Wait for POLLIN
                epoll_ctl(epollfd, EPOLL_CTL_MOD, dd->fd, &((struct epoll_event){.events=POLLIN, .data.ptr = dd}));
                return;
            } else if (err == WOLFSSL_ERROR_WANT_WRITE) {
                // Wait for POLLOUT
                epoll_ctl(epollfd, EPOLL_CTL_MOD, dd->fd, &((struct epoll_event){.events=POLLOUT, .data.ptr = dd}));
                return;
            }
            // If it's another error, the handshake failed. Close connection.
        }
    }

    // --- Handshake is finished! ---
    
    if (events & POLLIN) {
        // Read the encrypted HTTP request from the client
        // (Your logic here)
        // forward to dohfd or check cache
    }
    
    if (events & POLLOUT) {
        // Write the encrypted HTTP response back to the client
        // (Your logic here)
        // if cache hit write https repsonse to client
    }
}
