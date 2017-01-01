
open System

open BenchmarkDotNet.Attributes
open BenchmarkDotNet.Running
//open FSharpx.Collections
open System.Collections
open System.Collections.Generic

open FSharpz.Collections.Mutable

let rng = Random()
let max = pown 10 9

type IPriorityQueue<'T when 'T : comparison> =
    inherit System.Collections.IEnumerable
    inherit System.Collections.Generic.IEnumerable<'T>

    ///returns true if the queue has no elements
    abstract member IsEmpty : bool with get

    ///returns a new queue with the element added to the end
    abstract member Insert : 'T -> IPriorityQueue<'T>

    ///returns option first element
    abstract member TryPeek : unit -> 'T option

    ///returns the first element
    abstract member Peek : unit -> 'T

    ///returns the count of the elements
    abstract member Length : int

    //returns the option first element and tail
    abstract member TryPop : unit -> ('T * IPriorityQueue<'T>) option

    ///returns the first element and tail
    abstract member Pop : unit -> 'T * IPriorityQueue<'T> 

type Heap<'T when 'T : comparison> (length : int, data : HeapData<'T>) =
    let mutable hashCode = None
    member internal this.heapData = data
    member internal this.heapLength = length

    override this.GetHashCode() =
        match hashCode with
        | None ->
            let mutable hash = 1
            for x in this do
                hash <- 31 * hash + Unchecked.hash x
            hashCode <- Some hash
            hash
        | Some hash -> hash

    override this.Equals(other) =
        match other with
        | :? Heap<'T> as y -> 
            if this.Length <> y.Length then false 
            else
                if this.GetHashCode() <> y.GetHashCode() then false
                else Seq.forall2 (Unchecked.equals) this y
        | _ -> false

    static member private merge newLength (h1 : HeapData<'T>) (h2 : HeapData<'T>) : Heap<'T> = 
        match h1, h2 with
        | E, h -> Heap(newLength, h)
        | h, E -> Heap(newLength, h)
        | T(x, xs), T(y, ys) ->
            if x <= y then Heap(newLength, T(y, h1::ys)) else Heap(newLength, T(x, h2::xs))

    //http://lorgonblog.wordpress.com/2008/04/06/catamorphisms-part-two
    static member private foldHeap nodeF leafV (h : list<HeapData<'T>>) = 

        let rec loop (h : list<HeapData<'T>>) cont =
            match h with
            | T(a, h')::tl -> loop h'  (fun lacc ->  
                                    loop tl (fun racc -> 
                                    cont (nodeF a lacc racc))) 
            | _ -> cont leafV
        
        loop h (fun x -> x)

    static member private inOrder (h : list<HeapData<'T>>) = (Heap.foldHeap (fun x l r acc -> l (x :: (r acc))) (fun acc -> acc) h) [] 
 
    static member internal ofSeq (s:seq<'T>) : Heap<'T> = 
        if Seq.isEmpty s then Heap(0, E)
        else
            let len, h' =
                 Seq.fold (fun (lnth, (h : 'T HeapData)) x -> 
                    match h with 
                    | E -> 1, T(x, [])
                    | T(y, ys) ->
                        if x <= y then (lnth + 1), T(y, T(x, [])::ys) else (lnth + 1), T(x, T(y, ys)::[])
                    ) (0,E) s
            Heap(len, h')
    
    ///O(1) worst case. Returns the min or max element.   
    member this.Head = 
        match data with
        | E -> raise (new System.Exception("Heap is empty"))
        | T(x, _) -> x

    ///O(1) worst case. Returns option first min or max element.
    member this.TryHead = 
        match data with
        | E -> None
        | T(x, _) -> Some(x)

    ///O(log n) amortized time. Returns a new heap with the element inserted.
    member this.Insert x  = 
        Heap.merge (length + 1) (T(x, [])) data

    ///O(1). Returns true if the heap has no elements.
    member this.IsEmpty = 
        match data with
        | E -> true 
        | _ -> false

    ///O(n). Returns the count of elememts.
    member this.Length = length

    ///O(log n) amortized time. Returns heap from merging two heaps, both must have same descending.
    member this.Merge (xs : Heap<'T>) = 
        Heap.merge (length + xs.heapLength) data xs.heapData

    ///O(log n) amortized time. Returns heap option from merging two heaps.
    member this.TryMerge (xs : Heap<'T>) = 
        Some(Heap.merge (length + xs.heapLength) data xs.heapData)

    ///O(n log n). Returns heap reversed.
    member this.Rev() = 
        Heap<'T>.ofSeq (this :> seq<'T>)

    ///O(log n) amortized time. Returns a new heap of the elements trailing the head.
    member this.Tail() =

        let mergeData (h1 : HeapData<'T>) (h2 : HeapData<'T>) : HeapData<'T> = 
            match h1, h2 with
            | E, h -> h
            | h, E -> h
            | T(x, xs), T(y, ys) ->
                if x <= y then T(y, h1::ys) else T(x, h2::xs)

        match data with
        | E -> raise (new System.Exception("Heap is empty"))
        | T(x, xs) -> 
            let combinePairs state item =
                match state with
                | Some p, l ->
                    (None, (mergeData item p)::l)
                | None, l ->
                    (Some item, l)
            
            let tail = 
                xs
                |> List.fold combinePairs (None, [])
                |> function
                   | Some i, l -> i::l
                   | None, l -> l
                |> List.fold mergeData E
            
            Heap((length - 1), tail)
      
    ///O(log n) amortized time. Returns option heap of the elements trailing the head.
    member this.TryTail() =
        match data with
        | E -> None
        | _ -> Some (this.Tail())

    ///O(log n) amortized time. Returns the head element and tail.
    member this.Uncons() = 
        match data with
        | E -> raise (new System.Exception("Heap is empty"))
        | T(x, xs) -> x, this.Tail() 

    ///O(log n) amortized time. Returns option head element and tail.
    member this.TryUncons() = 
        match data with
        | E -> None
        | T(x, xs) -> Some(x, this.Tail())

    interface IEnumerable<'T> with

        member this.GetEnumerator() = 
            let e = 
                let listH = data::[]
                Heap.inOrder listH |> List.sort |> List.rev |> List.toSeq

            e.GetEnumerator()

        member this.GetEnumerator() = (this :> _ seq).GetEnumerator() :> IEnumerator

    interface IPriorityQueue<'T>

        with
        member this.IsEmpty = this.IsEmpty
        member this.Insert element = this.Insert element :> IPriorityQueue<'T>
        member this.TryPeek() = this.TryHead
        member this.Peek() = this.Head
        member this.Length = this.Length

        member this.TryPop() = 
            match this.TryUncons() with
            | Some(element,newHeap) -> Some(element,newHeap  :> IPriorityQueue<'T>)
            | None -> None

        member this.Pop() = 
            let element,newHeap = this.Uncons()
            element,(newHeap  :> IPriorityQueue<'T>)

and HeapData<'T when 'T : comparison> =
    | E 
    | T of 'T * list<HeapData<'T>>

let emptyHeap<'T when 'T : comparison> = Heap<'T>(0, E) :> IPriorityQueue<'T>

type PriorityQueue () =
    let mutable list  : int list = []

    [<Params (2000, 20000, 200000, 2000000)>]
    member val public Length = 0 with get, set

    [<Setup>]
    member self.SetupData() =
        list <- [for i in 2..self.Length -> rng.Next(1, max)]

    [<Benchmark>]
    member self.MaxPriorityQueue () = PriorityQueue<int>(list)

    [<Benchmark>]
    member self.MaxPriorityQueueInsertingFromStart () = 
        let pq = PriorityQueue<int>()
        list |> List.iter pq.Enqueue

    [<Benchmark>]
    member self.FSharpxPriorityQueueInsertingFromStart () = 
        //let pq = PriorityQueue.empty true
        let pq = emptyHeap
        let rec insertIntoPriorityQueue xs (q: IPriorityQueue<IComparable>) =
            match xs with
            | [] -> ()
            | h::tail -> insertIntoPriorityQueue tail (q.Insert(h))
        insertIntoPriorityQueue list pq

[<EntryPoint>]
let main argv = 
    (BenchmarkSwitcher[|typeof<PriorityQueue>|]).Run argv
    |> string |> printfn "%s"
    0
