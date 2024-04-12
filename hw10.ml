(** Part 1: Parsing *)
let parse_exp_tests : (string * exp option) list = [
  ("", None)
]

let rec exp_parser i = 
  let open Parser in
  let identifier, keyword =
    let keywords = ["true"; "false"; "let"; "in"; "end"; "if"; "then"; "else"; "fn"; "rec"] in
    identifier_except keywords, keyword_among keywords
  in 
  
  let atomic_exp_parser : exp Parser.t = 
    first_of [
      map (fun i -> ConstI i) int_digits;
      (keyword "true" |>> of_value (ConstB true));
      (keyword "false" |>> of_value (ConstB false));
      map (fun x -> Var x) identifier;
      between (symbol "(") (symbol ")") exp_parser;
    ]
  in

  let applicative_exp_parser : exp Parser.t = 
    atomic_exp_parser |*> fun first_exp ->
      many atomic_exp_parser |> map (
        List.fold_left (fun acc e -> Apply(acc, e)) first_exp)
  in 

  let let_binding_parser : exp Parser.t =
    keyword "let" |>> first_of [
      (between (symbol "(") (symbol ")") (sep_by_1 identifier (symbol ",")) |*> fun params ->
          symbol "=" |>> 
          exp_parser |*> fun exprs ->
            keyword "in" |>> exp_parser |*> fun body ->
                symbol "end" |>> (match params with
                    | [] | [_] -> fail
                    | x :: y :: _ -> of_value (LetComma(x, y, exprs, body))
                  ));
      (identifier |*> fun var ->
          symbol "=" |>> exp_parser |*> fun expr ->
              keyword "in" |>> exp_parser |*> fun body ->
                  symbol "end" |>> of_value (Let(var, expr, body)))
    ]
  in

  let if_then_else_parser : exp Parser.t =
    keyword "if" |>> exp_parser |*> fun b ->
        keyword "then" |>> exp_parser |*> fun t ->
            keyword "else" |>> exp_parser |*> fun f ->
                of_value (If(b, t, f))
  in

  let rec_parser : exp Parser.t =
    keyword "rec" |>> identifier |*> fun f ->
        optional (symbol ":" |>> typ_parser) |*> fun tOpt ->
          symbol "=>" |>> exp_parser |*> fun e ->
              of_value (Rec(f, tOpt, e))
  in

  let fn_parser : exp Parser.t =
    keyword "fn" |>> identifier |*> fun arg ->
        optional (symbol ":" |>> typ_parser) |*> fun tOpt ->
          symbol "=>" |>> exp_parser |*> fun e ->
              of_value (Fn(arg, tOpt, e))
  in

  let negation_exp_parser : exp Parser.t =
    optional (symbol "-") |*> fun n -> 
      applicative_exp_parser |> map (fun e ->
          match n with
          | Some _ -> PrimUop (Negate, e)
          | None -> e)
  in

  let multiplicative_exp_parser x =
    let multiplicative = 
      left_assoc_op (symbol "*") negation_exp_parser (fun e1 _ e2 -> PrimBop (e1, Times, e2)) 
    in
    multiplicative x
  in
  
  let additive_exp_parser x =
    let operator_parser = 
      first_of [
        symbol "+" |>> of_value (fun e1 e2 -> PrimBop(e1, Plus, e2));
        symbol "-" |>> of_value (fun e1 e2 -> PrimBop(e1, Minus, e2));
      ]
    in
    let additive =
      left_assoc_op operator_parser multiplicative_exp_parser (fun acc -> fun op_func -> op_func acc)
    in
    additive x
  in

  let comparative_op_parser : (exp -> exp -> exp) Parser.t =
    first_of [
      symbol "=" |>> of_value (fun e1 e2 -> PrimBop(e1, Equals, e2));
      symbol "<" |>> of_value (fun e1 e2 -> PrimBop(e1, LessThan, e2))
    ]
  in

  let comparative_exp_parser : exp Parser.t =
    first_of [ 
      (non_assoc_op comparative_op_parser additive_exp_parser (fun e op -> op e));
    ]
  in

  let tuple_exp_parser : exp Parser.t = 
    between (symbol "(") (symbol ")") (
      map2 (fun e1 e2 -> Comma(e1, e2)) comparative_exp_parser (symbol "," |>> comparative_exp_parser)
    ) 
  in
  
  let comma_pair_exp_parser =
    map3 (fun e1 _ e2 -> Comma (e1, e2)) comparative_exp_parser (symbol ",") comparative_exp_parser
  in
  
  let exp_parser_impl = 
    first_of [
      let_binding_parser;
      fn_parser;
      rec_parser;
      comma_pair_exp_parser; 
      tuple_exp_parser; 
      if_then_else_parser; 
      comparative_exp_parser; 
      additive_exp_parser;  
      multiplicative_exp_parser;  
      negation_exp_parser; 
      atomic_exp_parser;
      applicative_exp_parser;
    ]
  in
  exp_parser_impl i

(** DO NOT Change This Definition *)
let parse_exp : string -> exp option =
  let open Parser in
  run (between spaces eof exp_parser)
(** Part 2: Type Inference *)
let typ_infer_test_helper_tests : ((Context.t * exp) * typ option) list = [
  ((Context.empty, ConstB true), Some Bool)
]

let rec typ_infer (ctx : Context.t) (e : exp) : typ =
  match e with
  | ConstI _ -> Int

  | ConstB _ -> Bool
  
  | PrimBop (e1, bop, e2) ->
      let ((t1, t2), t3) = bop_type bop in
      if typ_infer ctx e1 = t1 && typ_infer ctx e2 = t2 then t3
      else raise TypeInferenceError
  
  | PrimUop (uop, e') ->

      let (t1, t2) = uop_type uop in
      if typ_infer ctx e' = t1 then t2
      else raise TypeInferenceError

  | If (e', e1, e2) ->
      if typ_infer ctx e' <> Bool then raise TypeInferenceError
      else 
        let t1 = typ_infer ctx e1 in
        if t1 = typ_infer ctx e2 then t1
        else raise TypeInferenceError

  | Comma (e1, e2) -> Pair (typ_infer ctx e1, typ_infer ctx e2)

  | LetComma (x, y, e1, e2) -> 
      let Pair (tx, ty) = typ_infer ctx e1 in 
      (* let ctx' = Context.extend ctx (x, tx) in *)
      let ctx'' = Context.extend (Context.extend ctx (x, tx)) (y, ty) in 
      typ_infer ctx'' e2

  | Fn (x, Some t, e') -> 
      let arrow_type = Arrow (t, typ_infer (Context.extend ctx (x, t)) e') in
      arrow_type

  | Apply (e1, e2) ->
      let t1 = typ_infer ctx e1 in
      let t2 = typ_infer ctx e2 in
      (match t1 with
       | Arrow (tx, ty) ->
           if tx = t2 then ty
           else raise TypeInferenceError
       | _ -> raise TypeInferenceError)

  | Rec (f, Some t, e') ->  
      let ctx' = Context.extend ctx (f, t) in
      let inferred_type = typ_infer ctx' e' in
      if inferred_type = t then t
      else raise TypeInferenceError

  | Let (x, e1, e2) ->
      let t1 = typ_infer ctx e1 in
      let ctx' = Context.extend ctx (x, t1) in
      typ_infer ctx' e2

  | Var x ->
      begin
        match Context.lookup ctx x with
        | Some t -> t
        | None -> raise TypeInferenceError
      end
  (** You can ignore these cases for Part 2 *)
  | Fn (_, None, _) -> raise IgnoredInPart2
  | Rec (_, None, _) -> raise IgnoredInPart2

(** DO NOT Change This Definition *)
let typ_infer_test_helper ctx e =
  try
    Some (typ_infer ctx e)
  with
  | TypeInferenceError -> None

(** Part 3: Substitution & Evaluation *)
let free_vars_test_helper_tests : (exp * ident list) list = [
  (ConstI 0, []);
  (Var "x", ["x"]); 
]

let rec free_vars (e : exp) : IdentSet.t =
  match e with
  | ConstI _ -> IdentSet.empty
  | PrimBop (e1, _, e2) -> IdentSet.union (free_vars e1) (free_vars e2)
  | PrimUop (_, e') -> free_vars e'

  | ConstB _ -> IdentSet.empty
  | If (e', e1, e2) -> IdentSet.union (free_vars e') (IdentSet.union (free_vars e1) (free_vars e2))

  | Comma (e1, e2) -> IdentSet.union (free_vars e1) (free_vars e2)
  | LetComma (x, y, e1, e2) -> IdentSet.union (free_vars e1) (IdentSet.remove y (IdentSet.remove x (free_vars e2)))
                                 
  | Fn (x, _, e') -> IdentSet.remove x (free_vars e')
  | Apply (e1, e2) -> IdentSet.union (free_vars e1) (free_vars e2)

  | Rec (f, _, e') -> IdentSet.remove f (free_vars e')

  | Let (x, e1, e2) -> IdentSet.union (free_vars e1) (IdentSet.remove x (free_vars e2))
  | Var x -> IdentSet.singleton x


(** DO NOT Change This Definition *)
let free_vars_test_helper e = IdentSet.elements (free_vars e)

let subst_tests : (((exp * ident) * exp) * exp) list = [
  (((ConstI 5, "x"), PrimBop (ConstI 2, Plus, Var "x")), PrimBop (ConstI 2, Plus, ConstI 5))
]

let rec subst ((d, z) : exp * ident) (e : exp) : exp =
  (** [rename (x, e)] replace [x] appears in [e] with a fresh identifier
      and returns the fresh identifier and updated expression *)
  let rename ((x, e) : ident * exp) : ident * exp =
    let x' = fresh_ident x in
    (x', subst (Var x', x) e)
  in
  match e with
  | ConstI _ | ConstB _ -> e
  | PrimBop (e1, bop, e2) ->
      PrimBop (subst (d, z) e1, bop, subst (d, z) e2)
  | PrimUop (uop, e1) ->
      PrimUop (uop, subst (d, z) e1)
  | If (e1, e2, e3) ->
      If (subst (d, z) e1, subst (d, z) e2, subst (d, z) e3)
  | Comma (e1, e2) ->
      Comma (subst (d, z) e1, subst (d, z) e2)
  | LetComma (x, y, e1, e2) ->
      let e1' = subst (d, z) e1 in
      let e2', x', y' =
        if x = z || IdentSet.mem x (free_vars d) || y = z || IdentSet.mem y (free_vars d) then
          let (x', e2') = if x = z || IdentSet.mem x (free_vars d) then rename (x, e2) else (x, e2) in
          let (y', e2'') = if y = z || IdentSet.mem y (free_vars d) then rename (y, e2') else (y, e2') in
          (e2'', x', y')
        else (e2, x, y)
      in
      LetComma (x', y', e1', subst (d, z) e2')
  | Fn (x, tOpt, e') ->
      if x = z then Fn (x, tOpt, e')
      else if IdentSet.mem x (free_vars d) then
        let (x', e'') = rename (x, e') in
        Fn (x', tOpt, subst (d, z) e'')
      else Fn (x, tOpt, subst (d, z) e')
  | Apply (e1, e2) ->
      Apply (subst (d, z) e1, subst (d, z) e2)
  | Rec (x, tOpt, e') ->
      if x = z then Rec (x, tOpt, e')
      else if IdentSet.mem x (free_vars d) then
        let (x', e'') = rename (x, e') in
        Rec (x', tOpt, subst (d, z) e'')
      else Rec (x, tOpt, subst (d, z) e')
  | Let (x, e1, e2) ->
      let e1' = subst (d, z) e1 in
      if x = z then Let (x, e1', e2)
      else if IdentSet.mem x (free_vars d) then
        let (x', e2') = rename (x, e2) in
        Let (x', e1', subst (d, z) e2')
      else Let (x, e1', subst (d, z) e2)
          
  | Var x ->
      if x = z then d
      else e

let eval_test_helper_tests : (exp * exp option) list = [
  (Var "x", None);
  (ConstI 5, Some (ConstI 5));
  (PrimBop (ConstI 5, Minus, ConstI 5), Some (ConstI 0))
]

let rec eval (e : exp) : exp =
  match e with
  | ConstI _ | ConstB _ -> e
  | PrimBop (e1, bop, e2) ->
      begin
        match eval e1, eval e2 with
        | ConstI n1, ConstI n2 ->
            begin
              match bop with
              | Equals -> ConstB (n1 = n2)
              | LessThan -> ConstB (n1 < n2)
              | Plus -> ConstI (n1 + n2)
              | Minus -> ConstI (n1 - n2)
              | Times -> ConstI (n1 * n2)
            end
        | _ -> raise EvaluationStuck
      end
  | PrimUop (uop, e1) ->
      begin
        match eval e1 with
        | ConstI n -> ConstI (- n)
        | _ -> raise EvaluationStuck
      end
  | If (e1, e2, e3) ->
      begin
        match eval e1 with
        | ConstB true -> eval e2
        | ConstB false -> eval e3
        | _ -> raise EvaluationStuck
      end
  | Comma (e1, e2) ->
      let ev1, ev2 = eval e1, eval e2 in
      Comma (ev1, ev2)
  | LetComma (x, y, e1, e2) ->
      let v1 = eval e1 in
      begin
        match v1 with
        | Comma (vx, vy) -> subst (vx, x) (subst (vy, y) e2) |> eval
        | _ -> raise EvaluationStuck
      end
  | Fn (x, _, e') -> Fn (x, None, e')
  | Apply (e1, e2) ->
      let fn = eval e1 in
      let arg = eval e2 in
      begin
        match fn with
        | Fn (x, _, body) -> eval (subst (arg, x) body)
        | _ -> raise EvaluationStuck
      end
  | Rec (x, _, e') ->
      subst (Rec (x, None, e'), x) e' |> eval
  | Let (x, e1, e2) ->
      let v1 = eval e1 in
      subst (v1, x) e2 |> eval
  | Var _ -> raise EvaluationStuck

(** DO NOT Change This Definition *)
let eval_test_helper e =
  try
    Some (eval e)
  with
  | EvaluationStuck -> None


(** Part 4: Unification & Advanced Type Inference *)
let unify_test_case1 () =
  let x = new_tvar () in
  let y = new_tvar () in
  y := Some Int;
  (TVar x, TVar y)

let unify_test_case2 () =
  let x = new_tvar () in
  (TVar x, Arrow (TVar x, TVar x))

let unify_test_helper_tests : ((unit -> typ * typ) * bool) list = [
  ((fun () -> (Int, Int)), true);
  ((fun () -> (Int, Bool)), false);
  (unify_test_case1, true);
  (unify_test_case2, false)
]

let rec unify : typ -> typ -> unit =
  let rec occurs_check (x : typ option ref) (t : typ) : bool =
    let t = rec_follow_tvar t in
    match t with
    | Int -> false
    | Bool -> false
    | Pair (t1, t2) -> occurs_check x t1 || occurs_check x t2
    | Arrow (t1, t2) -> occurs_check x t1 || occurs_check x t2
    | TVar y -> is_same_tvar x y
                
  in
  fun ta tb ->
    let ta = rec_follow_tvar ta in
    let tb = rec_follow_tvar tb in
    match ta, tb with
    | Int, Int -> ()
    | Bool, Bool -> ()
    | Pair (ta1, ta2), Pair (tb1, tb2) -> 
        unify ta1 tb1;
        unify ta2 tb2
    | Arrow (ta1, ta2), Arrow (tb1, tb2) -> 
        unify ta1 tb1;
        unify ta2 tb2
    | TVar xa, TVar xb when is_same_tvar xa xb -> ()
    | TVar xa, _ -> 
        if occurs_check xa tb then
          raise OccursCheckFailure  
        else
          xa := Some tb
    | _, TVar _ -> unify tb ta
    | _, _ -> raise UnificationFailure 
  

(* Part 4.2 Below *)

(** DO NOT Change This Definition *)
let unify_test_helper f =
  let ta, tb = f () in
  try
    unify ta tb; true
  with
  | UnificationFailure -> false
  | OccursCheckFailure -> false

let adv_typ_infer_test_case1 =
  let x = new_tvar () in
  ((Context.empty, Fn ("y", None, Var "y")), Some (Arrow (TVar x, TVar x)))

let adv_typ_infer_test_helper_tests : ((Context.t * exp) * typ option) list = [
  adv_typ_infer_test_case1
]

let rec adv_typ_infer (ctx : Context.t) (e : exp) : typ =
  match e with
  | ConstI _ -> Int
  | PrimBop (e1, bop, e2) -> 
      let ((t1, t2), t3) = bop_type bop in
      unify (adv_typ_infer ctx e1) t1;
      unify (adv_typ_infer ctx e2) t2;
      t3
  | PrimUop (uop, e') -> 
      let (t1, t2) = uop_type uop in
      unify (adv_typ_infer ctx e') t1;
      t2
  | ConstB _ -> Bool
  | If (e', e1, e2) -> 
      let t = adv_typ_infer ctx e' in
      unify t Bool;
      let t1 = adv_typ_infer ctx e1 in
      let t2 = adv_typ_infer ctx e2 in
      unify t1 t2;
      t1
  | Comma (e1, e2) -> 
      Pair (adv_typ_infer ctx e1, adv_typ_infer ctx e2)
  | LetComma (x, y, e1, e2) -> 
      let t1 = adv_typ_infer ctx e1 in
      (match t1 with
       | Pair (tx, ty) ->
           let ctx_extended = Context.extend (Context.extend ctx (x, tx)) (y, ty) in
           adv_typ_infer ctx_extended e2
       | _ -> raise TypeInferenceError)
  | Fn (x, Some t, e') -> 
      let ctx_extended = Context.extend ctx (x, t) in
      Arrow (t, adv_typ_infer ctx_extended e')
  | Fn (x, None, e') -> 
      let x_type = new_tvar () in
      let ctx_extended = Context.extend ctx (x, TVar x_type) in
      let body_type = adv_typ_infer ctx_extended e' in
      Arrow (TVar x_type, body_type)
  | Apply (e1, e2) -> 
      let t1 = adv_typ_infer ctx e1 in
      let t2 = adv_typ_infer ctx e2 in
      let t3 = new_tvar () in
      unify t1 (Arrow (t2, TVar t3));
      TVar t3
  | Rec (f, Some t, e') -> 
      let ctx_extended = Context.extend ctx (f, t) in
      unify t (adv_typ_infer ctx_extended e');
      t
  | Rec (f, None, e') -> 
      let f_type_var = new_tvar () in
      let ctx_extended = Context.extend ctx (f, TVar f_type_var) in
      let inferred_body_type = adv_typ_infer ctx_extended e' in
      unify (TVar f_type_var) inferred_body_type;
      TVar f_type_var
  | Let (x, e1, e2) -> 
      let t1 = adv_typ_infer ctx e1 in
      let ctx_extended = Context.extend ctx (x, t1) in
      adv_typ_infer ctx_extended e2
  | Var x -> 
      match Context.lookup ctx x with
      | Some (TVar {contents = Some t}) -> t
      | Some t -> t
      | None -> raise TypeInferenceError

(** DO NOT Change This Definition *)
let adv_typ_infer_test_helper ctx e =
  try
    Some (adv_typ_infer ctx e)
  with
  | UnificationFailure -> None
  | OccursCheckFailure -> None
  | TypeInferenceError -> None

(**
 ************************************************************
You Don't Need to Modify Anything After This Line
************************************************************

Following definitions are the helper entrypoints
so that you can do some experiments in the top-level.
Once you implement [exp_parser], [typ_infer], and [eval],
you can test them with [infer_main] in the top-level.
Likewise, once you implement [exp_parser], [adv_typ_infer], and [eval],
you can test them with [adv_infer_main] in the top-level.
*)
let infer_main exp_str =
  match parse_exp exp_str with
  | None -> raise ParserFailure
  | Some e ->
      print_string "input expression       : "; print_exp e; print_newline ();
      let t = typ_infer Context.empty e in
      print_string "type of the expression : "; print_typ t; print_newline ();
      print_string "evaluation result      : "; print_exp (eval e); print_newline ()

let adv_infer_main exp_str =
  match parse_exp exp_str with
  | None -> raise ParserFailure
  | Some e ->
      print_string "input expression       : "; print_exp e; print_newline ();
      let t = adv_typ_infer Context.empty e in
      print_string "type of the expression : "; print_typ t; print_newline ();
      print_string "evaluation result      : "; print_exp (eval e); print_newline ()
