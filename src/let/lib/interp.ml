open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Unpair(id1,id2,e1,e2) ->
    eval_expr e1 >>=
    pair_of_pairVal >>= fun (l,r) ->
    extend_env id1 l >>+
    extend_env id2 r >>+
    eval_expr e2
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | IsEmpty(e) -> 
    eval_expr e >>=
    tree_of_treeVal >>= fun t ->
    return (BoolVal (t = Empty))
  | EmptyTree(_t) -> 
    return (TreeVal(Empty))
  | Node(e1,e2,e3) -> 
    eval_expr e1 >>= fun d ->
    eval_expr e2 >>=
    tree_of_treeVal >>= fun l ->
    eval_expr e3 >>=
    tree_of_treeVal >>= fun r ->
    return (TreeVal(Node(d,l,r)))
  | CaseT(e1,e2,id1,id2,id3,e3) -> 
    eval_expr e1 >>=
    tree_of_treeVal >>= fun t ->
    begin
    match t with
    | Empty -> eval_expr e2
    | Node(d,l,r) -> extend_env id1 d >>+
                     extend_env id2 (TreeVal l) >>+
                     extend_env id3 (TreeVal r) >>+
                     eval_expr e3
    end
  | Record(fs) -> let l = List.map (fun (_,(_,e)) -> e) fs in
                        eval_exprs l >>= fun v -> let x =
                        List.map2 (fun (s,_) x -> (s,x)) fs v in
                        if has_dup_fields x
                        then error "Record: duplicate fields"
                        else return (RecordVal x)
  | Proj(e,id) -> 
    eval_expr e >>=
    rec_of_recordVal >>= fun r -> begin
    match List.assoc_opt id r with
    | Some f -> return f
    | None -> error "Proj: field does not exist"
    end
  | _ -> failwith "Not implemented yet!"
and
  eval_exprs : expr list -> (exp_val list) ea_result =
  fun es ->
  match es with
  | [] -> return []
  | h::t -> eval_expr h >>= fun i ->
    eval_exprs t >>= fun l ->
    return (i::l)

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


