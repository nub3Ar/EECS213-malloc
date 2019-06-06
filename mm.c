/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "The 213 Struggle bus drivers",
    /* First member's full name */
    "Yijing Barry Zhang",
    /* First member's email address */
    "yijingzhang2021@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Sizheng Zhang",
    /* Second member's email address (leave blank if none) */
    "sizhengzhang2021@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define WORD_SIZE 4
#define DOUBLE_SIZE 8
#define CHUNKSIZE (1<<12)

/*
* MAX --- return max of x and y
*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*
* Pack a size and allocated bit into a word
*/
#define PACK(size, alloc) ((size)|(alloc))

/*Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define WRITE(p, val) (*(unsigned int *)(p) = (val))

//read the size field at the address
#define GET_SIZE(p) (GET(p) & ~0x7)

//read the allocated field at the address
#define GET_ALLOC(p) (GET(p) & 0x1)

//get header and footer address of a given block address
#define GETHEADER(p) ((char *)(p) - WORD_SIZE)
#define GETFOOTER(p) ((char *)(p) + GET_SIZE(GETHEADER(p)) - DOUBLE_SIZE)
#define GETPRED(p) ((char *)(p))
#define GETSUCC(p) ((char *)(p + WORD_SIZE))
#define GETADDRESS(p) (*(void **)(p))

//get the next block
#define NEXTB(p) ((char *)(p) + GET_SIZE(((char *)(p) - WORD_SIZE)))

//get the previous block
#define PREVB(p) ((char *)(p) - GET_SIZE(((char *)(p) - DOUBLE_SIZE)))

/* rounds up to the nearest multiple of DOUBLE_SIZE */
#define ALIGN(size) (((size) + (DOUBLE_SIZE-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Helper function declaration
static void* extend_heap(size_t words);
static void* find_fit (size_t asize);
static void* coalesce(void *block_p);
static void place (void *bp, size_t asize);
static void remove_block(void *block_p);
static void insert_block(void *block_p)

// variable to initialize the linkedlist
static char *heap_p = NULL;
static int MAXSIZE = 13;
static void *seg_list[MAXSIZE];

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    char* heap_p;
    // create the heap
    if(((heap_p = mem_sbrk(WORD_SIZE * 4)) == (void*)-1)){
        return -1;
    }

    //initialize linkedlist
    for (int i = 0; i<MAXSIZE; i++)
        seg_list[i] = NULL;

    //initialize prologue
    WRITE(heap_p, 0); //alignment padding
    WRITE(heap_p + (1 * WORD_SIZE), PACK(DOUBLE_SIZE, 1)); //prologue header
    WRITE(heap_p + (2 * WORD_SIZE), PACK(DOUBLE_SIZE, 1)); //prologue footer
    WRITE(heap_p + (3 * WORD_SIZE), PACK(0, 1)); //epilogue header
    heap_p += DOUBLE_SIZE;

    //extend the heap for with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WORD_SIZE) == NULL) return -1;
    return 0;
}

/*
 * extend_heap - extend the heap with a free block
*/
static void* extend_heap(size_t words){
    void* block_p;
    size_t align_size = (words % 2) ? (words+1) * WORD_SIZE : words * WORD_SIZE;

    //get alignment size based on the size given
    align_size = ALIGN(align_size);

    if ((long)(block_p = mem_sbrk(align_size)) == -1)
        return NULL;

    //initialize header and footer for free block as well as new epilogue header
    WRITE(GETHEADER(block_p), PACK(DOUBLE_SIZE, 0)); //free block header
    WRITE(GETFOOTER(block_p), PACK(DOUBLE_SIZE, 0)); //free block footer

    // initialize next and prev pointers 
    WRITE(GETSUCC(block_p), NULL);
    WRITE(GETPRED(block_p), NULL);

    WRITE(GETHEADER(NEXTB(block_p)), PACK(0, 1)); //next block header

    return coalesce(block_p);


}

/*
 * coalesce - combine free blocks
*/
static void* coalesce(void *block_p){
    size_t prev_alloc = GET_ALLOC(GETFOOTER(PREVB(block_p))); //get previous alloc bool
    size_t next_alloc = GET_ALLOC(GETHEADER(NEXTB(block_p))); //get next alloc bool
    size_t size = GET_SIZE(GETHEADER(block_p)); //get next alloc size

    //case 1: previous alloc and next alloc both used
    if(prev_alloc && next_alloc){
        return block_p;
    }
    
    //case 2: next alloc is free, previous alloc is not, free footer and header
    //of the next block
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(GETHEADER(NEXTB(block_p)));
        WRITE(GETFOOTER(block_p), PACK(size, 0));
        WRITE(GETHEADER(block_p), PACK(size, 0));
    }

    //case 3: next alloc is not free, previous alloc is free, free header and footer
    //of the previous block
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(GETHEADER(PREVB(block_p)));
        WRITE(GETFOOTER(block_p), PACK(size, 0));
        WRITE(GETHEADER(PREVB(block_p)), PACK(size, 0));
        block_p = PREVB(block_p);
    }

    //case 4: both the previous and next alloc is free, free footer of next
    //and header of previous
    else {
        size += GET_SIZE(GETHEADER(PREVB(block_p)))+GET_SIZE(GETFOOTER(NEXTB(block_p)));
        WRITE(GETHEADER(PREVB(block_p)), PACK(size, 0));
        WRITE(GETFOOTER(NEXTB(block_p)), PACK(size, 0));
        block_p = PREVB(block_p);
    }

    return block_p;
    
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests*/
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DOUBLE_SIZE)
        asize = 2 * DOUBLE_SIZE;
    else
        asize = DOUBLE_SIZE * ((size + DOUBLE_SIZE + (DOUBLE_SIZE-1)) / DOUBLE_SIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize))!= NULL){
        place(bp, asize);
        return bp;
    }

    /*NO fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WORD_SIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
    /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    
    }
    */
}


static void* find_fit (size_t asize){
    /* First-fit search */
    void *bp;
    for (int index = find_ll_index(asize); index < MAXSIZE; index++){
         bp= seg_list[index];
         while (bp != NULL){
            if(GET_SIZE(GETHEADER(bp))>=size) return bp;
            bp=(void *)(GETSUCC(bp));
         }

    }
    /*head_p not defined here */
    return NULL; /* no fit */
}


static void place (void *bp, size_t asize){
    size_t csize = GET_SIZE(GETHEADER(bp));
    //if the current block is at least 16 bytes, write in
    if((csize - asize)>= 2 * DOUBLE_SIZE){
        WRITE(GETHEADER(bp), PACK(asize, 1));
        WRITE(GETFOOTER(bp), PACK(asize, 1));
        bp = NEXTB(bp);
        WRITE(GETHEADER(bp), PACK(csize - asize, 0));
        WRITE(GETFOOTER(bp), PACK(csize - asize, 0));
    }
    //else, we mark the block as used for trash
    else{
        WRITE(GETHEADER(bp), PACK(csize, 1));
        WRITE(GETFOOTER(bp), PACK(csize, 1));
    }  
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){
    size_t b_size = GET_SIZE(GETHEADER(ptr));
    //free the header and the footer
    WRITE(GETHEADER(ptr), PACK(b_size, 0)); //free header
    WRITE(GETFOOTER(ptr), PACK(b_size, 0)); //free footer
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    //if ptr is null, functions the same as malloc
    if (ptr == NULL){
        mm_malloc(size);
    }

    //if size is 0, functions the same as free
    if (size == 0){
        mm_free(ptr);
        return 0;
    }
    
    //get new size with alignment and old size
    size_t new_size = ALIGN(size) + DOUBLE_SIZE;
    size_t old_size = GET_SIZE(GETHEADER(ptr)); 

    //if the current block is big enough with alignment
    //we can just return the current block
    if (new_size <= old_size){
        return ptr;
    }

    //when new size is larger than old size, extend to next block and
    //check again to see if it's large enough and if it's already allocated
    else if((old_size + GET_SIZE(GETHEADER(NEXTB(ptr)))) >= new_size && !GET_ALLOC(GETHEADER(NEXTB(ptr)))){
        size_t com_size = old_size +  GET_SIZE(GETHEADER(NEXTB(ptr)));
        WRITE(GETHEADER(ptr), PACK(com_size, 1));
        WRITE(GETFOOTER(ptr), PACK(com_size, 1));
        return ptr;
    }
    //If all else fails, we need to allocate a new piece of memory
    //and copy the block to fit the requested size
    else{
        void *new_ptr = mm_malloc(size);
        if (new_ptr == NULL) return 0;
        memcpy(new_ptr, ptr, old_size - DOUBLE_SIZE - ALIGN(size));
        mm_free(ptr);

        return new_ptr;

    }

}

static void remove_block(void *block_p){
    //calculat the size of the block that we want to take out
    size_t bsize = GET_SIZE(HDRP(block_p));

    //find its position in the seg_list
    int index = find_ll_index (bsize);
    char *pred = GETPRED(block_p)
    char *succ = GETSUCC(block_p)

    //remove the block from the appropriate position in the seg_list
    if (pred == NULL && succ == NULL) seg_list[index] ==NULL;
    else if(pred == NULL && succ != NULL){
        GETADDRESS(GETPRED(GETADDRESS(succ))) = NULL;
        seg_list[index] = GETADDRESS(succ);

    }
    else if (pred!= NULL && succ == NULL){
       GETADDRESS(GETSUCC(GETADDRESS(pred))) = NULL;

    }
    else{
        GETADDRESS(GETSUCC(GETADDRESS(pred))) = GETADDRESS(succ);
        GETADDRESS(GETPRED(GETADDRESS(succ))) = GETADDRESS(pred);
    }
}

static void insert_block(void *block_p){
    //calculat the size of the block that we want to insert
    size_t bsize = GET_SIZE(HDRP(block_p));

    //find its position in the seg_list
    int index = find_ll_index (bsize);
    void* head = seg_list[index];
    //if there is nothing in the index of the list
    if(head == NULL){
        seg_list[index] = block_p;
        GETADDRESS(GETPRED(block_p)) = NULL;
        GETADDRESS(GETSUCC(block_p)) = NULL;
    }

    //if the head is not NULL
    else{
        sizt_t bpsize = GET_SIZE(GETHEADER(block_p));
        void* temp = NULL;
        while ((head!= NULL) && (GET_SIZE(GETHEADER(head))<bpsize)) {
            temp = head;
            head = GETADDRESS(GETSUCC(head));
        } //traverse the seg_list

        //** head is the place where we insert the new block; that is, we should insert block in front of head
        //when it gets to the end of the list, make block_p the last element of the seg_list
        if (head ==NULL){
            GETADDRESS(GETSUCC(temp)) = block_p;
            GETADDRESS(GETPRED(block_p)) = temp;
            GETADDRESS(GETSUCC(block_p)) = NULL;     
        }
        else{ 
            //put the new block at the beginning of the seg_list
            if (head == seg_list[index]){
                GETADDRESS(GETPRED(head)) = block_p;
                GETADDRESS(GETSUCC(block_p)) = head;
                GETADDRESS(GETPRED(block_p)) =NULL;
                seg_list[index] = block_p;
            }

            //insert in the middle (this situation occurs when the bpsize < side of head)
            else{
                GETADDRESS(GETSUCC(GETADDRESS(GETPRED(head)))) = bp;
                GETADDRESS(GETPRED(block_p)) = GETPRED(head);
                GETADDRESS(GETSUCC(block_p)) = head;
                GETADDRESS(GETPRED(head)) = bp;

            }
        }
    }
}


static int find_ll_index (sizt_t size)
{
    if (size<=8)
        return 0;
    else if(size <=16)
        return 1;
    else if (size<=32)
        return 2;
    else if (size<=64)
        return 3;
    else if (size<=128)
        return 4;
    else if (size<=256)
        return 5;
    else if (size<=512)
        return 6;
    else if (size<=1024)
        return 7;
    else if (size<= 2048)
        return 8;
    else if (size<= 4096)
        return 9;
    else
        return 10;
}
