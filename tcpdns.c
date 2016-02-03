#include <unistd.h>
#include "droproot.h"
#include "exit.h"
#include "env.h"
#include "uint32.h"
#include "uint16.h"
#include "ip4.h"
#include "tai.h"
#include "buffer.h"
#include "timeoutread.h"
#include "timeoutwrite.h"
#include "open.h"
#include "seek.h"
#include "cdb.h"
#include "stralloc.h"
#include "strerr.h"
#include "str.h"
#include "byte.h"
#include "case.h"
#include "dns.h"
#include "scan.h"
#include "qlog.h"
#include "response.h"
#include "ip6.h"
#include "clientloc.h"
#include "edns0.h"

extern int respond(char *,char *,char *);

#define FATAL "tcpdns: fatal: "

void nomem()
{
  strerr_die2x(111,FATAL,"out of memory");
}
void die_truncated()
{
  strerr_die2x(111,FATAL,"truncated request");
}
void die_netwrite()
{
  strerr_die2sys(111,FATAL,"unable to write to network: ");
}
void die_netread()
{
  strerr_die2sys(111,FATAL,"unable to read from network: ");
}
void die_outside()
{
  strerr_die2x(111,FATAL,"unable to locate information in data.cdb");
}
void die_cdbread()
{
  strerr_die2sys(111,FATAL,"unable to read data.cdb: ");
}
void die_cdbformat()
{
  strerr_die3x(111,FATAL,"unable to read data.cdb: ","format error");
}

int safewrite(int fd,char *buf,unsigned int len)
{
  int w;

  w = timeoutwrite(60,fd,buf,len);
  if (w <= 0) die_netwrite();
  return w;
}

char netwritespace[1024];
buffer netwrite = BUFFER_INIT(safewrite,1,netwritespace,sizeof netwritespace);

void print(char *buf,unsigned int len)
{
  char tcpheader[2];
  uint16_pack_big(tcpheader,len);
  buffer_put(&netwrite,tcpheader,2);
  buffer_put(&netwrite,buf,len);
  buffer_flush(&netwrite);
}

static char *zone;
unsigned int zonelen;
char typeclass[4];

int fdcdb;
buffer bcdb;
char bcdbspace[1024];

void get(char *buf,unsigned int len)
{
  int r;

  while (len > 0) {
    r = buffer_get(&bcdb,buf,len);
    if (r < 0) die_cdbread();
    if (!r) die_cdbformat();
    buf += r;
    len -= r;
  }
}

char ip[16];
unsigned long port;
char clientloc[2];

struct tai now;
char data[32767];
uint32 dlen;
uint32 dpos;

void copy(char *buf,unsigned int len)
{
  dpos = dns_packet_copy(data,dlen,dpos,buf,len);
  if (!dpos) die_cdbread();
}

void doname(stralloc *sa)
{
  static char *d;
  dpos = dns_packet_getname(data,dlen,dpos,&d);
  if (!dpos) die_cdbread();
  if (!stralloc_catb(sa,d,dns_domain_length(d))) nomem();
}

int build(stralloc *sa,char *q,int flagsoa,char id[2])
{
  unsigned int rdatapos;
  char misc[20];
  char type[2];
  char recordloc[2];
  char ttl[4];
  char ttd[8];
  struct tai cutoff;

  dpos = 0;
  copy(type,2);
  if (flagsoa) if (byte_diff(type,2,DNS_T_SOA)) return 0;
  if (!flagsoa) if (byte_equal(type,2,DNS_T_SOA)) return 0;

  if (!stralloc_copyb(sa,id,2)) nomem();
  if (!stralloc_catb(sa,"\204\000\0\0\0\1\0\0\0\0",10)) nomem();
  copy(misc,1);
  if ((misc[0] == '=' + 1) || (misc[0] == '*' + 1)) {
    --misc[0];
    copy(recordloc,2);
    if (byte_diff(recordloc,2,clientloc)) return 0;
  }
  if (misc[0] == '*') {
    if (flagsoa) return 0;
    if (!stralloc_catb(sa,"\1*",2)) nomem();
  }
  if (!stralloc_catb(sa,q,dns_domain_length(q))) nomem();
  if (!stralloc_catb(sa,type,2)) nomem();

  copy(ttl,4);
  copy(ttd,8);
  if (byte_diff(ttd,8,"\0\0\0\0\0\0\0\0")) {
    tai_unpack(ttd,&cutoff);
    if (byte_equal(ttl,4,"\0\0\0\0")) {
      if (tai_less(&cutoff,&now)) return 0;
      uint32_pack_big(ttl,2);
    }
    else
      if (!tai_less(&cutoff,&now)) return 0;
  }

  if (!stralloc_catb(sa,DNS_C_IN,2)) nomem();
  if (!stralloc_catb(sa,ttl,4)) nomem();
  if (!stralloc_catb(sa,"\0\0",2)) nomem();
  rdatapos = sa->len;

  if (byte_equal(type,2,DNS_T_SOA)) {
    doname(sa);
    doname(sa);
    copy(misc,20);
    if (!stralloc_catb(sa,misc,20)) nomem();
  }
  else if (byte_equal(type,2,DNS_T_NS) || byte_equal(type,2,DNS_T_PTR) || byte_equal(type,2,DNS_T_CNAME)) {
    doname(sa);
  }
  else if (byte_equal(type,2,DNS_T_MX)) {
    copy(misc,2);
    if (!stralloc_catb(sa,misc,2)) nomem();
    doname(sa);
  }
  else
    if (!stralloc_catb(sa,data + dpos,dlen - dpos)) nomem();

  if (sa->len > 65535) die_cdbformat();
  uint16_pack_big(sa->s + rdatapos - 2,sa->len - rdatapos);
  return 1;
}

void netread(char *buf,unsigned int len)
{
  int r;

  while (len > 0) {
    r = timeoutread(60,0,buf,len);
    if (r == 0) _exit(0);
    if (r < 0) die_netread();
    buf += r; len -= r;
  }
}

char tcpheader[2];
char buf[512];
uint16 len;

static char seed[128];

int main()
{
  unsigned int pos;
  char header[12];
  char qtype[2];
  char qclass[2];
  const char *x;

  droproot(FATAL);
  dns_random_init(seed);

  x = env_get("REMOTE_ADDR");
  if (x && ip6_scan(x,ip))
    ;
  else
    byte_zero(ip,16);

  x = env_get("REMOTE_PORT");
  if (!x) x = "0";
  scan_ulong(x,&port);

  for (;;) {
    netread(tcpheader,2);
    uint16_unpack_big(tcpheader,&len);
    if (len > 512) strerr_die2x(111,FATAL,"excessively large request");
    netread(buf,len);

    pos = dns_packet_copy(buf,len,0,header,12); if (!pos) die_truncated();
    if (header[2] & 254) strerr_die2x(111,FATAL,"bogus query");
    if (header[4] || (header[5] != 1)) strerr_die2x(111,FATAL,"bogus query");

    pos = dns_packet_getname(buf,len,pos,&zone); if (!pos) die_truncated();
    zonelen = dns_domain_length(zone);
    pos = dns_packet_copy(buf,len,pos,qtype,2); if (!pos) die_truncated();
    pos = dns_packet_copy(buf,len,pos,qclass,2); if (!pos) die_truncated();

    if (byte_diff(qclass,2,DNS_C_IN) && byte_diff(qclass,2,DNS_C_ANY))
      strerr_die2x(111,FATAL,"bogus query: bad class");

    pos = check_edns0(header, buf, len, pos);
    if (!pos) die_truncated();

    qlog(ip,port,header,zone,qtype," ");

    if (byte_equal(qtype,2,DNS_T_AXFR)) {
      strerr_die2x(111,FATAL,"disallowed zone transfer request");
    }
    else {
      if (!response_query(zone,qtype,qclass)) nomem();
      response[2] |= 4;
      case_lowerb(zone,zonelen);
      response_id(header);
      response[3] &= ~128;
      if (!(header[2] & 1)) response[2] &= ~1;
      if (!respond(zone,qtype,ip)) die_outside();
      print(response,response_len);
    }
  }
}
