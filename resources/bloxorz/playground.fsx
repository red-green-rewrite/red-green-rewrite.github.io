open System.Collections.Generic

let bfs idof fanout node =
    let queue = Queue([node])
    let visited = HashSet()

    // DSL
    let enqueue = queue.Enqueue
    let dequeue = queue.Dequeue
    let empty () = queue.Count = 0
    let mark = idof >> visited.Add >> ignore
    let test = idof >> visited.Contains >> not

    // algorithm
    seq {
        while not (empty ()) do
            let current = dequeue ()
            mark current
            yield current
            current |> fanout |> Seq.filter test |> Seq.iter enqueue
    }

let trace traverse idof fanout node =
    let node' = (node, [])
    let idof' (node, _) = idof node
    let fanout' (node, actions) =
        node |> fanout |> Seq.map (fun (n, a) -> (n, a :: actions))
    traverse idof' fanout' node'

let demo1 () =
    let tree =
        [
            1, [2; 3; 4]
            2, [5; 6]
            5, [9; 10]
            4, [7; 8]
            7, [11; 12]
        ]
        |> Map.ofSeq

    let fanout node = tree |> Map.tryFind node |> Option.defaultValue []
    1 |> bfs id fanout |> List.ofSeq

let demo2 () =
    let tree =
        [
            1, [2; 3; 4]
            2, [5; 6]
            5, [9; 10]
            4, [7; 8]
            7, [11; 12]
        ]
        |> Map.ofSeq

    let fanout node = tree |> Map.tryFind node |> Option.defaultValue [] |> List.map (fun n -> n, node)
    1 |> trace bfs id fanout

open System.IO


let scan root =
    let node = DirectoryInfo(root)
    let fanout (node: DirectoryInfo) = try node.EnumerateDirectories("*") with | _ -> Seq.empty
    let idof (node: DirectoryInfo) = node.FullName
    node |> bfs idof fanout |> Seq.map idof |> Seq.toList

//demo2 () |> Seq.map (fun (h, t) -> h :: t) |> List.ofSeq
demo2 () |> Seq.map (List.Cons >> List.rev) |> List.ofSeq

//----

type Position = int * int
type Bloxor = Position * Position
type Move = | North | East | South | West
type Path = Bloxor * Move list
type World = { A: Position; B: Position; IsValid: Position -> bool }

let infiniteWorld a b = { A = a; B = b; IsValid = fun _ -> true }
let makeBloxor (position: Position): Bloxor = (position, position)
let (|IsStanding|IsHorizontal|IsVertical|) (bloxor: Bloxor) =
    let ((ax, ay), (bx, by)) = bloxor
    match bx - ax, by - ay with
    | 0, 0 -> IsStanding
    | 1, 0 -> IsHorizontal
    | 0, 1 -> IsVertical
    | _ -> failwithf "Invalid bloxor (%d,%d) (%d,%d)" ax ay bx by

let moveBloxor (bloxor: Bloxor) (direction: Move): Bloxor =
    let shiftX x1 x2 ((ax, ay), (bx, by)) = (ax + x1, ay), (bx + x2, by)
    let shiftY y1 y2 ((ax, ay), (bx, by)) = (ax, ay + y1), (bx, by + y2)
    let move =
        match bloxor, direction with
        | IsStanding, North -> shiftY -2 -1
        | IsStanding, East -> shiftX 1 2
        | IsStanding, South -> shiftY 1 2
        | IsStanding, West -> shiftX -2 -1
        | IsHorizontal, North -> shiftY -1 -1
        | IsHorizontal, East -> shiftX 2 1
        | IsHorizontal, South -> shiftY 1 1
        | IsHorizontal, West -> shiftX -1 -2
        | IsVertical, North -> shiftY -1 -2
        | IsVertical, East -> shiftX 1 1
        | IsVertical, South -> shiftY 2 1
        | IsVertical, West -> shiftX -1 -1
    move bloxor

let solveWorld (world: World): Move list option =
    // DSL
    let isValid (a, b) = world.IsValid a && world.IsValid b
    let isFinal (a, b) = a = world.B && b = world.B
    let validMoves bloxor =
        [North; South; East; West]
        |> Seq.map (fun direction -> (moveBloxor bloxor direction, direction))
        |> Seq.filter (fun (bloxor, _) -> isValid bloxor)

    // action!
    let node = makeBloxor world.A
    let idof ((ax, ay), (bx, by)) = sprintf "%d.%d.%d.%d" ax ay bx by
    let fanout = validMoves
    trace bfs idof fanout node |> Seq.tryFind (fst >> isFinal) |> Option.map (snd >> List.rev)

infiniteWorld (0, 0) (1, 0) |> solveWorld
infiniteWorld (0, 0) (9, 9) |> solveWorld

let parseWorld lines =
    let map =
        lines
        |> Seq.mapi (fun y l -> l |> Seq.mapi (fun x c -> (x, y), c))
        |> Seq.collect id
        |> Map.ofSeq
    let a = map |> Map.findKey (fun _ c -> c = 'A')
    let b = map |> Map.findKey (fun _ c -> c = 'B')
    let valid k = map |> Map.tryFind k |> Option.filter (fun c -> c <> ' ') |> Option.isSome
    { A = a; B = b; IsValid = valid }

let world = [
    "      xxxxxxx"
    "xxxx  xxx  xx"
    "xxxxxxxxx  xxxx"
    "xAxx       xxBx"
    "xxxx       xxxx"
    "            xxx"
]
world |> parseWorld |> solveWorld

type Jug = | A | B
type Action =
    | Empty of Jug
    | Fill of Jug
    | Transfer of Jug * Jug
type State =
    { A: int; B: int; MaxA: int; MaxB: int }
    static member Create (a, b) = { A = 0; B = 0; MaxA = a; MaxB = b }
    member x.Max j = match j with | A -> x.MaxA | B -> x.MaxB
    member x.Get j = match j with | A -> x.A | B -> x.B
    member private x.Set (j, v) = match j with | A -> { x with A = v } | B -> { x with B = v }
    member private x.Add (j, v) = x.Set(j, x.Get j + v)
    member x.Empty j = x.Set(j, 0)
    member x.Fill j = x.Set(j, x.Max j)
    member x.Transfer j k =
        let amount = min (x.Get j) (x.Max k - x.Get k)
        x.Add(j, -amount).Add(k, amount)


let applyAction (state: State) action =
    match action with
    | Empty j -> state.Empty j
    | Fill j -> state.Fill j
    | Transfer (j, k) when j <> k -> state.Transfer j k
    | _ -> failwithf "Invalid move: %A" action

let saveNewYork target state =
    let idof s = sprintf "%d.%d" s.A s.B
    let fanout s =
        [Empty A; Empty B; Fill A; Fill B; Transfer (A, B); Transfer (B, A)]
        |> Seq.map (fun action -> (applyAction s action, action))
    let isDone s = s.A = target || s.B = target

    trace bfs idof fanout state
    |> Seq.tryFind (fun (state, _) -> isDone state)
    |> Option.map (fun (_, actions) -> List.rev actions)

let newYork = State.Create(3, 5)
let solution = newYork |> saveNewYork 4
let mutable curr = newYork
for action in solution |> Option.defaultValue [] do
    let next = applyAction curr action
    printfn "%d/%d -> %A -> %d/%d" curr.A curr.B action next.A next.B
    curr <- next

State.Create(113, 97) |> saveNewYork 66
State.Create(12, 6) |> saveNewYork 4