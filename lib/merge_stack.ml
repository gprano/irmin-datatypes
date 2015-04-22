(*
 * Copyright (c) 2014 Benjamin Farinier <benjamin.farinier@ens-lyon.fr>
 * Copyright (c) 2014 Thomas Gazagnaire <thomas@gazagnaire.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*)

open Lwt
open Irmin.Merge.OP

module Log = Log.Make(struct let section = "STACK" end)

exception Empty

type error = [ `Corrupted | `Invalid_access | `Todo ]
exception Error of error

type stats = {
  ops: int;
  reads: int;
  writes: int;
}

let string_of_stats t =
  Printf.sprintf "%i\t%f\t%f%!"
    t.ops
    ((float t.reads)  /. (float t.ops))
    ((float t.writes) /. (float t.ops))

module type S = sig
  include Irmin.Contents.S
  type elt
  val create : unit -> t Lwt.t
  val length : t -> int Lwt.t
  val is_empty : t -> bool Lwt.t
  val push : t -> elt -> t Lwt.t
  val pop_exn : t -> (elt * t) Lwt.t
  val pop : t -> (elt * t) option Lwt.t
  val peek_exn : t -> (elt * t) Lwt.t
  val peek : t -> (elt * t) option Lwt.t
  val dump : t -> string Lwt.t
  val stats : t -> stats
end

module type Config = sig
  val conf: Irmin.config
  val task: string -> Irmin.task
end

module Make
    (AO: Irmin.AO_MAKER)
    (K: Irmin.Hash.S)
    (V: Tc.S0)
    (P: Irmin.Path.S)
    (Config: Config)
= struct

  module Path = P

  module C = struct

    (*
     * Type of index, which are stack accessor.
     * 'push' is the number of push applied to the stack since its creation,
     * 'pop' is the number of pop applied to the stack since its creation,
     * 'top' is the key of the stack top element,
    *)
    type index = {
      push  : int;
      pop   : int;
      top   : K.t;
    }

    module Index = Tc.Biject
        (Tc.Pair (Tc.Pair(Tc.Int)(Tc.Int))(K))
        (struct
          type t = index
          let to_t ((push, pop), top) = {push; pop; top}
          let of_t {push; pop; top} = (push, pop), top
        end)

    (*
     * Type of node, which are elements manipulated by stack operations.

    *)
    type node = {
      next    : K.t option;
      next2   : K.t option;
      elt     : K.t option;
      branch  : index option;
    }

    module KO = Tc.Option (K)
    module Node = Tc.Biject
        (Tc.Pair(Tc.Pair(KO)(KO))(Tc.Pair(KO)(Tc.Option(Index))))
        (struct
          type t = node
          let to_t ((next, next2), (elt, branch)) =
            {next; next2; elt; branch}
          let of_t {next; next2; elt; branch} =
            (next, next2), (elt, branch)
        end)

    (*
     * Type of store elements.
    *)
    type t =
      | Index of Index.t
      | Node  of Node.t
      | Elt   of V.t
    with compare

    let equal_node n1 n2 =
      Node.compare n1 n2 = 0

    let to_json = function
      | Index i -> `O [ "index", Index.to_json i ]
      | Node n  -> `O [ "node" , Node.to_json n ]
      | Elt e   -> `O [ "elt"  , V.to_json e ]

    let of_json = function
      | `O [ "index", j ] -> Index (Index.of_json j)
      | `O [ "node" , j ] -> Node (Node.of_json j)
      | `O [ "elt"  , j ] -> Elt (V.of_json j)
      | j -> Ezjsonm.parse_error j "C.of_json"

    let equal x y = match x, y with
      | Index x, Index y -> Index.equal x y
      | Node x, Node y -> Node.equal x y
      | Elt x, Elt y -> V.equal x y
      | _ -> false

    let hash = Hashtbl.hash

    (* FIXME: slow *)
    let to_string t = Ezjsonm.to_string (to_json t)
    let of_string s = of_json (Ezjsonm.from_string s)
    let write t buf =
      let str = to_string t in
      let len = String.length str in
      Cstruct.blit_from_string str 0 buf 0 len;
      Cstruct.shift buf len
    let read buf =
      Mstruct.get_string buf (Mstruct.length buf)
      |> of_string
    let size_of t =
      let str = to_string t in
      String.length str

  end

  let (incr_read, incr_write, get_read, get_write) =
    let count_read = ref 0 in
    let count_write = ref 0 in
    (
      (fun () -> incr count_read),
      (fun () -> incr count_write),
      (fun () -> !count_read),
      (fun () -> !count_write)
    )

  module Store = struct

    module S = AO(K)(C)

    include S

    let create () =
      create Config.conf Config.task

    let read t k =
      incr_read ();
      S.read t k

    let read_exn t k =
      incr_read ();
      S.read_exn t k

    let read_free t k =
      S.read_exn t k

    let add t v =
      incr_write ();
      S.add t v

  end

  (*
   * Type of a queue.
   * 'index' is the index of the queue in its store,
   * 'root' is the key of the 'empty' element of store.
  *)
  type queue = {
    index: C.Index.t;
    root : K.t;
  }

  module T = Tc.Biject (Tc.Pair (C.Index)(K))
      (struct
        type t = queue
        let to_t (index, root) = {index; root}
        let of_t {index; root} = (index, root)
      end)
  include T

  type elt = V.t

  let empty = {
    C.next = None;
    C.next2 = None;
    C.elt = None;
    C.branch = None;
  }

  (*
   * Create a new queue in the store 'store'.
   * 'top' and 'bottom' are pointed on the 'empty' node.
  *)
  let create () =
    Store.create () >>= fun store ->
    Store.add (store "create") (C.Node empty) >>= fun root ->
    let index = {
      C.push = 0;
      C.pop = 0;
      C.top = root;
    } in
    return { index; root }

  let length t =
    return (t.index.C.push - t.index.C.pop)

  let is_empty t =
    return (t.index.C.push = t.index.C.pop)
  
  (*
   * Add a new node in the push list, and move the index on.
   * The new index is NOT added in the store, ie the queue is NOT updated.
  *)
  let push q elt =

    Store.create () >>= fun store ->
    let index = q.index in
    let root = q.root in

    Store.add (store "push 1") (C.Elt elt) >>= fun key_elt ->
    let node = {
      C.next = Some index.C.top;
      C.next2 = None;
      C.elt = Some key_elt;
      C.branch = None;
    } in
    Store.add (store "push 2") (C.Node node) >>= fun key_node ->
    let index = {
      C.push = index.C.push + 1;
      C.pop = index.C.pop;
      C.top = key_node;
    } in
    return { index; root }


  
  let push_branch q branch =

    Store.create () >>= fun store ->
    let index = q.index in
    let root = q.root in

    let node = {
      C.next = Some index.C.top;
      C.next2 = None;
      C.elt = None;
      C.branch = Some branch;
    } in
    Store.add (store "push_branch") (C.Node node) >>= fun key_node ->
    let index = {
      C.push = index.C.push;
      C.pop = index.C.pop;
      C.top = index.C.top;
    } in
    return { index; root }

  (*
   * Move the index of the queue to the next element.
   * The new index is NOT added in the store, ie the queue is NOT updated.
   * Return None if the queue is empty.
  *)
  let rec pop q =

    Store.create () >>= fun store ->
    let index = q.index in
    let root = q.root in

    if index.C.push = index.C.pop then
      return None
    else
      Store.read_exn (store "pop 1") index.C.top >>= fun node ->
      match node with
      | C.Index _
      | C.Elt _ -> fail (Error `Corrupted)
      | C.Node node ->
        match node.C.elt with
        | None -> fail (Error `Todo)
        | Some elt ->
          Store.read_exn (store "pop 2") elt >>= fun elt ->
          match elt with
          | C.Index _
          | C.Node _ -> fail (Error `Corrupted)
          | C.Elt elt ->
            let key = (match node.C.next with
                | None -> root
                | Some key -> key) in
            let index = {
              C.push = index.C.push;
              C.pop = index.C.pop + 1;
              C.top = key;
            } in

            return (Some (elt, { index; root }))

  (*
   * Move the index of the queue to the next element.
   * The new index is NOT added in the store, ie the queue is NOT updated.
   * Raise Empty if the queue is empty.
  *)
  let rec pop_exn q =

    Store.create () >>= fun store ->
    let index = q.index in
    let root = q.root in

    if index.C.push = index.C.pop then
      fail Empty
    else
      Store.read_exn (store "pop_exn") index.C.top >>= fun node ->
      match node with
      | C.Index _
      | C.Elt _ -> fail (Error `Corrupted)
      | C.Node node ->
        match node.C.elt with
        | None -> fail (Error `Todo)
        | Some elt ->
          Store.read_exn (store "pop_exn") elt >>= fun elt ->
          match elt with
          | C.Index _
          | C.Node _ -> fail (Error `Corrupted)
          | C.Elt elt ->
            let key = (match node.C.next with
                | None -> root
                | Some key -> key) in
            let index = {
              C.push = index.C.push;
              C.pop = index.C.pop + 1;
              C.top = key;
            } in

            return (elt, { index; root })

  (*
   * Read the elt associated to the top node of the queue.
   * Return None if the queue is empty.
  *)
  let rec peek q =

    Store.create () >>= fun store ->
    let index = q.index in

    if index.C.push = index.C.pop then
      return None
    else
      Store.read_exn (store "peek 1") index.C.top >>= fun node ->
      match node with
      | C.Index _
      | C.Elt _ -> fail (Error `Corrupted)
      | C.Node node ->
        match node.C.elt with
        | None -> fail (Error `Todo)
        | Some elt ->
          Store.read_exn (store "peek 2") elt >>= fun elt ->
          match elt with
          | C.Index _
          | C.Node _ -> fail (Error `Corrupted)
          | C.Elt elt ->
            return (Some (elt, q))

  (*
   * Read the elt associated to the top node of the queue.
   * Raise Empty if the queue is empty.
  *)
  let rec peek_exn q =

    Store.create () >>= fun store ->
    let index = q.index in

    if index.C.push = index.C.pop then
      raise Empty
    else
      Store.read_exn (store "peek_exn 1") index.C.top >>= fun node ->
      match node with
      | C.Index _
      | C.Elt _ -> fail (Error `Corrupted)
      | C.Node node ->
        match node.C.elt with
        | None -> fail (Error `Todo)
        | Some elt ->
          Store.read_exn (store "peek_exn 2") elt >>= fun elt ->
          match elt with
          | C.Index _
          | C.Node _ -> fail (Error `Corrupted)
          | C.Elt elt ->
            return (elt, q)

  (* problem of the merge and join will make you dump several times thee same element.
     solve this with a ref hash table ? *)
  
  let rec dump q =

    Store.create () >>= fun store ->

    let rec from_top queue node =
      match node.C.next with
      | None -> (
          match node.C.elt with
          | None -> return (Printf.sprintf (if C.equal_node node empty then "Empty%!"
                                     else "None%!"))
          | Some key -> 
            Store.read_free (store "from_top 1")  key >>= fun elt ->
            return (Printf.sprintf "Some %s%!" (C.to_string elt))
        )
      | Some next -> (
          Store.read_free (store "from_top 2") next >>= fun next ->
          match next with
          | C.Index _
          | C.Elt _ -> assert false
          | C.Node next -> (
              from_top queue next >>= fun string ->
              match node.C.elt with
              | None ->return (
		  match node.C.branch with
                  | None -> Printf.sprintf "Noneatall -> %s%!" string
                  | Some i -> Printf.sprintf "Nonebutbranch: %s :endbranch -> %s%!" (Lwt_main.run (dump {index = i; root = q.root})) string
		)
              | Some elt ->
                Store.read_free (store "from_top 3") elt >>= fun elt ->
                return (Printf.sprintf "Some %s -> %s%!" (C.to_string elt) string)
            )
        )
    in

    Store.read_free (store "from_bottom 4") q.index.C.top >>= fun top ->
    match top with
    | C.Index _
    | C.Elt _ -> assert false
    | C.Node top ->
      from_top q top >>= fun string_top ->
      let string =
        Printf.sprintf "push: %i, pop: %i\nfrom top: %s\n\n%!"
          q.index.C.push q.index.C.pop string_top;
      in return string

  let stats q =
    let ops = q.index.C.push + q.index.C.pop in
    let reads = get_read () in
    let writes = get_write () in
    { ops; reads; writes }

  let merge: Path.t -> t option Irmin.Merge.t =
    
    let merge ~old q1 q2 =
      Store.create () >>= fun store ->
      old () >>= function  (* FIXME *)
      | `Conflict _ | `Ok None -> conflict "merge"
      | `Ok (Some old) ->
        assert K.(q1.root = q2.root && old.root = q1.root);
        let root = q1.root in
        let node = {
          C.next = Some q1.index.C.top;
          C.next2 = Some q2.index.C.top;
          C.elt = None;
          C.branch = None; } in
        Store.add (store "merge_node") (C.Node node) >>= fun key_node ->
        let index = {
          C.push = q1.index.C.push + q2.index.C.push - old.index.C.push;
          C.pop = q1.index.C.pop + q2.index.C.pop - old.index.C.push;
          C.top = key_node;
        } in
        ok {index; root}
    in

    fun _path -> Irmin.Merge.option (module T) merge


end
