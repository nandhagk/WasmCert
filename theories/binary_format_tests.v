(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         datatypes_properties check_toks operations.

Open Scope string_scope.
Import Stdlib.Strings.String.StringSyntax.
Open Scope list_scope.

(** The five sign-extension opcodes agree with validity, printing and parsing. **)
Definition extension_cases : list (number_type * N * Byte.byte) :=
  (T_i32, 8%N, xc0) :: (T_i32, 16%N, xc1) ::
  (T_i64, 8%N, xc2) :: (T_i64, 16%N, xc3) :: (T_i64, 32%N, xc4) :: nil.

Lemma extension_opcodes :
  List.map (fun '(t, n, b) =>
    (unop_type_agree t (Unop_extend n),
     binary_of_expr (BI_unop t (Unop_extend n) :: nil),
     run_parse_be (b :: nil))) extension_cases =
  List.map (fun '(t, n, b) =>
    (true, b :: x0b :: nil, Some (BI_unop t (Unop_extend n)))) extension_cases.
Proof. vm_compute. reflexivity. Qed.

(** Widths around the legal ones, including zero and large widths, are rejected. **)
Definition invalid_extension_widths : list N :=
  0%N :: 1%N :: 7%N :: 9%N :: 15%N :: 17%N :: 31%N ::
  33%N :: 64%N :: 128%N :: 4294967295%N :: nil.

Lemma invalid_extensions :
  List.map (fun n =>
    (unop_type_agree T_i32 (Unop_extend n),
     unop_type_agree T_i64 (Unop_extend n))) invalid_extension_widths =
  List.map (fun _ => (false, false)) invalid_extension_widths /\
  unop_type_agree T_i32 (Unop_extend 32) = false.
Proof. vm_compute. split; reflexivity. Qed.

Lemma float_extensions_invalid n :
  unop_type_agree T_f32 (Unop_extend n) = false /\
  unop_type_agree T_f64 (Unop_extend n) = false.
Proof. vm_compute. split; reflexivity. Qed.

(** Ordinary integer and floating unary operations keep their carrier types. **)
Lemma ordinary_unops_valid oi ofl :
  unop_type_agree T_i32 (Unop_i oi) = true /\
  unop_type_agree T_i64 (Unop_i oi) = true /\
  unop_type_agree T_f32 (Unop_f ofl) = true /\
  unop_type_agree T_f64 (Unop_f ofl) = true /\
  unop_type_agree T_f32 (Unop_i oi) = false /\
  unop_type_agree T_f64 (Unop_i oi) = false /\
  unop_type_agree T_i32 (Unop_f ofl) = false /\
  unop_type_agree T_i64 (Unop_f ofl) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Reinterpretation has exactly four opcodes, all with equal byte widths. **)
Definition reinterpret_cases : list (number_type * number_type * Byte.byte) :=
  (T_i32, T_f32, xbc) :: (T_i64, T_f64, xbd) ::
  (T_f32, T_i32, xbe) :: (T_f64, T_i64, xbf) :: nil.

Lemma reinterpret_opcodes :
  List.map (fun '(t2, t1, b) =>
    (cvtop_valid t2 CVO_reinterpret t1 None,
     binary_of_expr (BI_cvtop t2 CVO_reinterpret t1 None :: nil),
     run_parse_be (b :: nil))) reinterpret_cases =
  List.map (fun '(t2, t1, b) =>
    (true, b :: x0b :: nil, Some (BI_cvtop t2 CVO_reinterpret t1 None)))
    reinterpret_cases.
Proof. vm_compute. reflexivity. Qed.

Lemma cross_width_reinterpret_invalid :
  cvtop_valid T_i32 CVO_reinterpret T_f64 None = false /\
  cvtop_valid T_i64 CVO_reinterpret T_f32 None = false /\
  cvtop_valid T_f32 CVO_reinterpret T_i64 None = false /\
  cvtop_valid T_f64 CVO_reinterpret T_i32 None = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma reinterpret_requires_no_sign t2 t1 s :
  cvtop_valid t2 CVO_reinterpret t1 (Some s) = false.
Proof. destruct t2, t1, s; vm_compute; reflexivity. Qed.

Lemma reinterpret_requires_integer_float t :
  cvtop_valid t CVO_reinterpret t None = false /\
  cvtop_valid T_i32 CVO_reinterpret T_i64 None = false /\
  cvtop_valid T_i64 CVO_reinterpret T_i32 None = false /\
  cvtop_valid T_f32 CVO_reinterpret T_f64 None = false /\
  cvtop_valid T_f64 CVO_reinterpret T_f32 None = false.
Proof. destruct t; vm_compute; repeat split; reflexivity. Qed.

(** Indexed block types use s33; ordinary type indices still use u32. **)
Definition block_index_boundaries : list N :=
  0%N :: 63%N :: 64%N :: 122%N :: 127%N :: 128%N ::
  8191%N :: 8192%N :: 2147483648%N :: 4294967295%N :: nil.

Definition block_index_encodings : list (list Byte.byte) :=
  (x00 :: nil) :: (x3f :: nil) :: (xc0 :: x00 :: nil) ::
  (xfa :: x00 :: nil) :: (xff :: x00 :: nil) :: (x80 :: x01 :: nil) ::
  (xff :: x3f :: nil) :: (x80 :: xc0 :: x00 :: nil) ::
  (x80 :: x80 :: x80 :: x80 :: x08 :: nil) ::
  (xff :: xff :: xff :: xff :: x0f :: nil) :: nil.

Lemma block_index_raw_boundaries :
  List.map (fun bs => run_parse_be (x02 :: bs ++ x0b :: nil))
    block_index_encodings =
  List.map (fun n => Some (BI_block (BT_id n) nil)) block_index_boundaries.
Proof. vm_compute. reflexivity. Qed.

Lemma block_index_round_trips :
  List.map (fun n =>
    run_parse_be (x02 :: binary_of_block_type (BT_id n) ++ x0b :: nil))
    block_index_boundaries =
  List.map (fun n => Some (BI_block (BT_id n) nil)) block_index_boundaries.
Proof. vm_compute. reflexivity. Qed.

Lemma block_index_64_bytes :
  binary_of_block_type (BT_id 64%N) = (xc0 :: x00 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma block_index_122_bytes :
  binary_of_block_type (BT_id 122%N) = (xfa :: x00 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma negative_block_index_rejected :
  run_parse_be (x02 :: x7a :: x0b :: nil) = None /\
  run_parse_be (x02 :: xff :: x7f :: x0b :: nil) = None /\
  run_parse_be (x02 :: x80 :: x80 :: x80 :: x80 :: x70 :: x0b :: nil) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma oversized_block_index_rejected :
  run_parse_be (x02 :: x80 :: x80 :: x80 :: x80 :: x10 :: x0b :: nil) = None /\
  run_parse_be (x02 :: x80 :: x80 :: x80 :: x80 :: x80 :: x00 :: x0b :: nil) = None /\
  run_parse_be (x02 :: x80 :: x80 :: x80 :: x80 :: x80 :: nil) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Noncanonical encodings within five bytes remain allowed by the binary format. **)
Lemma padded_block_index_accepted :
  run_parse_be (x02 :: x80 :: x80 :: x80 :: x80 :: x00 :: x0b :: nil) =
    Some (BI_block (BT_id 0%N) nil).
Proof. vm_compute. reflexivity. Qed.

Lemma ordinary_type_index_unsigned :
  check_toks (x7a :: nil) (fun n => parse_typeidx (n := n)) =
    Running.Singleton 122%N.
Proof. vm_compute. reflexivity. Qed.

Lemma block_value_types_preserved :
  List.map (fun b => run_parse_be (x02 :: b :: x0b :: nil))
    (x40 :: x7f :: x7e :: x7d :: x7c :: x7b :: x70 :: x6f :: nil) =
  List.map (fun t => Some (BI_block (BT_valtype t) nil))
    (None :: Some (T_num T_i32) :: Some (T_num T_i64) ::
     Some (T_num T_f32) :: Some (T_num T_f64) :: Some (T_vec T_v128) ::
     Some (T_ref T_funcref) :: Some (T_ref T_externref) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton BI_unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton BI_nop.
Proof. vm_compute. reflexivity. Qed.

(** An example program. **)
Definition test :=
  BI_if (BT_valtype None) (BI_testop T_i64 TO_eqz :: nil) (BI_testop T_i64 TO_eqz :: nil).

(** Its byte representation. **)
Definition test_bytes : list Byte.byte :=
  x04 :: x40
  :: x50
  :: x05
  :: x50
  :: x0b
  :: x0b
  :: nil.

(** It is possible to display lists of bytes in a nice way using the following command:
[[
Compute hex_small_no_prefix_of_bytes test_bytes.
]]
**)

Lemma text_binary_correct : binary_of_expr (test :: nil) = test_bytes.
Proof. vm_compute. reflexivity. Qed.

Lemma text_parse_correct : run_parse_expr test_bytes = Some (test :: nil).
Proof. vm_compute. reflexivity. Qed.

(** It is possible to display programs in a nice way using the following command:
[[
Compute option_map pp_basic_instructions (run_parse_expr test_bytes).
]]
**)

(** Example from Wikipedia: https://en.wikipedia.org/wiki/WebAssembly#Code_representation
  This is the representation of a factorial function. **)
Definition test_wikipedia_byte : list Byte.byte :=
  x20 :: x00
  :: x50
  :: x04 :: x7e
  :: x42 :: x01
  :: x05
  :: x20 :: x00
  :: x20 :: x00
  :: x42 :: x01
  :: x7d
  :: x10 :: x00
  :: x7e
  :: x0b
  :: nil.

Definition test_wikipedia :=
  (BI_local_get 0%N
   :: BI_testop T_i64 TO_eqz
   :: BI_if (BT_valtype (Some (T_num T_i64)))
        (BI_const_num (VAL_int64 Wasm_int.Int64.one) :: nil)
        (BI_local_get 0%N
         :: BI_local_get 0%N
         :: BI_const_num (VAL_int64 Wasm_int.Int64.one)
         :: BI_binop T_i64 (Binop_i BOI_sub)
         :: BI_call 0%N
         :: BI_binop T_i64 (Binop_i BOI_mul) :: nil) :: nil).

Lemma test_wikipedia_correct : run_parse_bes test_wikipedia_byte = Some test_wikipedia.
Proof. vm_compute. reflexivity. Qed.

Definition empty_module := {|
  mod_types := nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma empty_module_round_trip : run_parse_module (binary_of_module empty_module) = Some empty_module.
Proof. vm_compute. reflexivity. Qed.

Definition module_type := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_round_trip :
  run_parse_module (binary_of_module module_type) = Some module_type.
Proof. vm_compute. reflexivity. Qed.

Definition module_type_fun := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_fun_round_trip :
  run_parse_module (binary_of_module module_type_fun) = Some module_type_fun.
Proof. vm_compute. reflexivity. Qed.

Definition module_42 := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 42))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_42_round_trip :
  run_parse_module (binary_of_module module_42) = Some module_42.
Proof. vm_compute. reflexivity. Qed.

Definition module_42_exported := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 42))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := cons {| modexp_name := String.list_byte_of_string "hello"; modexp_desc := MED_func 0%N; |} nil;
|}.

Lemma module_42_exported_round_trip :
  run_parse_module (binary_of_module module_42_exported) = Some module_42_exported.
Proof. vm_compute. reflexivity. Qed.

Definition module_tableops := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := (cons (Build_module_table (Build_table_type (Build_limits 0%N (Some 4%N)) T_funcref)) nil);
  mod_mems := nil;
                               mod_globals := nil;
  mod_elems := (cons (Build_module_element T_funcref (cons (cons (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1)))) nil) nil) (ME_active 0%N (cons (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1)))) nil))) nil);
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := cons {| modexp_name := String.list_byte_of_string "hello"; modexp_desc := MED_func 0%N; |} nil;
|}.

Lemma module_tableops_exported_round_trip :
  run_parse_module (binary_of_module module_tableops) = Some module_tableops.
Proof. vm_compute. reflexivity. Qed.
