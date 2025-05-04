#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"
/* ******************************************************************
Go Back N protocol. Adapted from J.F.Kurose
ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2
Network properties:
- one way network delay averages five time units (longer if there
are other messages in the channel for GBN), but can be larger
- packets can be corrupted (either the header or the data portion)
or lost, according to user-defined probabilities
- packets will be delivered in the order in which they were sent
(although some can be lost).
Modifications:
- removed bidirectional GBN code and other code not used by prac.
- fixed C style to adhere to current programming style
- added GBN implementation
**********************************************************************/
#define RTT 16.0 /* round trip time. MUST BE SET TO 16.0 when submitting
assignment */
#define WINDOWSIZE 6 /* the maximum number of buffered unacked packet */
#define SEQSPACE 12 /* the min sequence space for SR must be at least
2 * windowsize */
#define NOTINUSE (-1) /* used to fill header fields that are not being used */
/* generic procedure to compute the checksum of a packet. Used by both sender and
receiver
the simulator will overwrite part of your packet with 'z's. It will not
overwrite your
original checksum. This procedure must generate a different checksum to the
original if
the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet){
int checksum = 0;
int i;
checksum = packet.seqnum;
checksum += packet.acknum;
for(i=0; i<20; i++)
    checksum += (int)(packet.payload[i]);
return checksum;
}

bool IsCorrupted(struct pkt packet){
if(packet.checksum == ComputeChecksum(packet))
    return (false);
else
    return (true);
}

/********* Sender (A) variables and functions ************/
static struct pkt buffer[WINDOWSIZE]; /* array for storing packets waiting for ACK
*/
static int windowfirst, windowlast; /* array indexes of the first/last packet
awaiting ACK */
static int windowcount; /* the number of packets currently awaiting
an ACK */
static int A_nextseqnum; /* the next sequence number to be used by
the sender */
static bool waiting_for_ack;

/* called from layer 5 (application layer), passed the message to be sent to other
side */
void A_output(struct msg message){
struct pkt sendpkt;
int i;

/* if not blocked waiting on ACK */
if(windowcount < WINDOWSIZE){
    if(TRACE > 1)
        printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");
    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for(i=0; i<20 ; i++)
        sendpkt.payload[i] = message.data[i];

    sendpkt.checksum = ComputeChecksum(sendpkt);
    /* put packet in window buffer */
    /* windowlast will always be 0 for alternating bit; but not for GoBackN */
    windowlast = (windowlast + 1) % WINDOWSIZE;
    buffer[windowlast] = sendpkt;
    windowcount++;
    /* send out packet */
    if(TRACE > 0)
        printf("Sending packet %d to layer 3\n", sendpkt.seqnum);

    tolayer3(A, sendpkt);

    /* start timer for oldest unacked */
    if(windowcount == 0 || (A_nextseqnum % WINDOWSIZE) == windowfirst){
        starttimer(A,RTT);
        waiting_for_ack = true; 
    }
    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
} else{ /* if blocked, window is full */
if(TRACE > 0)
    printf("----A: New message arrives, send window is full\n");
window_full++;
}
}
/* called from layer 3, when a packet arrives for layer 4
In this practical this will always be an ACK as B never sends data.
*/
static bool PastAcked[WINDOWSIZE];

void A_input(struct pkt packet){
/* if received ACK is not corrupted */
if(!IsCorrupted(packet)){
    if(TRACE > 0)
        printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* check if new ACK or duplicate */
    if (windowcount != 0) {
        int seqfirst = buffer[windowfirst].seqnum;
        int seqlast = buffer[windowlast].seqnum;
        /* check case when seqnum has and hasn't wrapped */
        if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) || ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) {
    
            /* packet is a new ACK */
            if (TRACE > 0)
                printf("----A: ACK %d is not a duplicate\n",packet.acknum);
            new_ACKs++;
            
            /* cumulative acknowledgement - determine how many packets are ACKed */
            if(packet.acknum > seqfirst){
                PastAcked[packet.acknum % WINDOWSIZE] = true;
            } else{
                /* slide window by the number of packets ACKed */
                do {
                    windowcount--;
                    windowfirst = (windowfirst + 1) % WINDOWSIZE;
                    PastAcked[(windowfirst - 1 + WINDOWSIZE) % WINDOWSIZE] = false;
                } while(PastAcked[windowfirst] == true);
            }

            /* start timer again if there are still more unacked packets in window */
            stoptimer(A);
            if (windowcount > 0)
                starttimer(A, RTT);

        }
    } else if(TRACE > 0)
        printf ("----A: duplicate ACK received, do nothing!\n");
} else if(TRACE > 0)
    printf ("----A: corrupted ACK is received, do nothing!\n");
}

/* called when A's timer goes off */
void A_timerinterrupt(void){
if(TRACE > 0){
    printf ("----A: time out,resend packets!\n");
}

if (TRACE > 0)
    printf ("---A: resending packet %d\n", (buffer[windowfirst]).seqnum);

tolayer3(A, buffer[windowfirst]);
packets_resent++;
starttimer(A, RTT);       
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void){
int i;
/* initialise A's window, buffer and sequence number */
A_nextseqnum = 0; /* A starts with seq num 0, do not change this */
windowfirst = 0;
windowlast = -1; /* windowlast is where the last packet sent is stored.
new packets are placed in winlast + 1
so initially this is set to -1
*/
windowcount = 0;
waiting_for_ack = false;
for(i = 0; i < WINDOWSIZE; i++){
    PastAcked[i] = false;
}
}

/********* Receiver (B) variables and procedures ************/
static int expectedseqnum; /* the sequence number expected next by the receiver */
static struct pkt out_of_order_buffer[SEQSPACE];
static bool packet_received[SEQSPACE];
/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet){
struct pkt sendpkt;
int i;

/* if not corrupted and received packet is in order */
if(!IsCorrupted(packet)){
    int window_start = expectedseqnum;
    int window_end = (expectedseqnum + WINDOWSIZE - 1) % SEQSPACE;
    bool in_window = false;

    if(window_start <= window_end){
        if(packet.seqnum >= window_start && packet.seqnum <= window_end){
            in_window = true;
        }
    } else{
        if(packet.seqnum >= window_start || packet.seqnum <= window_end){
            in_window = true;
        }
    }
    
    if(in_window){
        if(packet.seqnum == expectedseqnum){
            if(TRACE > 0)
                printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
            packets_received++;
            /* deliver to receiving application */
            tolayer5(B, packet.payload);

            packet_received[packet.seqnum] = false;
            expectedseqnum = (expectedseqnum + 1) % SEQSPACE;

            while(packet_received[expectedseqnum]){
                if(TRACE > 4)
                    printf("----B: Sending old packet %d.\n",packet.seqnum);
                tolayer5(B, out_of_order_buffer[expectedseqnum].payload);
                packet_received[expectedseqnum] = false;
                expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
            }
        } else if(!packet_received[packet.seqnum]){
            if (TRACE > 0)
                printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");

            if(TRACE > 4)
                printf("----B: packet %d is received, wrong order.\n",packet.seqnum);
            packets_received++;
            packet_received[packet.seqnum] = true;
            out_of_order_buffer[packet.seqnum] = packet;
        }
        sendpkt.acknum = packet.seqnum;
    } else{
        if(packet.seqnum < expectedseqnum){
            sendpkt.acknum = packet.seqnum;
        } else{
            sendpkt.acknum = (expectedseqnum + SEQSPACE - 1) % SEQSPACE;
        }
    }
} else{
    if (TRACE > 0)
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");

    /* packet is corrupted resend last ACK */
    if(TRACE > 4)
        printf("----B: packet %d corrupted, resend ACK!\n", packet.seqnum);
    sendpkt.acknum = (expectedseqnum + SEQSPACE - 1) % SEQSPACE;
}

sendpkt.seqnum = 0;
/* we don't have any data to send. fill payload with 0's */
for(i=0; i<20 ; i++)
    sendpkt.payload[i] = '0';
/* computer checksum */
sendpkt.checksum = ComputeChecksum(sendpkt);
/* send out packet */
tolayer3(B, sendpkt);
}
/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void){
int i;
expectedseqnum = 0;
for(i = 0; i < SEQSPACE; i++){
    packet_received[i] = false;
}
}
/******************************************************************************
* The following functions need be completed only for bi-directional messages *
*****************************************************************************/
/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}
/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}