-- Prove2me | solution 1 for PfaffianRecognition.CoRP.polyProgram_pfAlg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:31:42.561186+00:00
-- url     : https://prove2.me/submissions/7c882726-ed48-449d-8e64-0b2020393ac3

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

namespace OAI.MetricKMedian.Binary.Automatic.Poly
open PolyProgram
set_option linter.unusedSectionVars false
variable {α β γ δ : Type} [Coding α] [Coding β] [Coding γ] [Coding δ]

theorem of_funext {f g : α → β} (h : Poly f) (e : ∀ x, f x = g x) : Poly g :=
  (funext e) ▸ h

@[fun_prop] theorem nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem nat_div : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem bool_xor : Poly (fun x : Bool × Bool => xor x.1 x.2) := ⟨PolyProgram.boolXor⟩

@[fun_prop] theorem nat_mod_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) := comp nat_mod (pair hf hg)
@[fun_prop] theorem bool_xor_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xor (f x) (g x)) := comp (f := fun x : Bool × Bool => xor x.1 x.2) bool_xor (pair hf hg)

/-- Length of the encoding of a value. -/
theorem enc_length : Poly (fun y : α => (enc y).length) := by
  let P : PolyProgram enc id (enc : α → List Bool) :=
    (PolyProgram.identity id).recode enc (fun _ => rfl) (fun _ => rfl)
  exact ⟨(P.comp PolyProgram.wordAsList).comp (PolyProgram.listLength encodeBool false)⟩

/-- Evaluation of a polynomial with natural coefficients (binary in, binary out). -/
theorem polynomial_eval (B : Polynomial ℕ) : Poly (fun n : ℕ => B.eval n) := by
  induction B using Polynomial.induction_on with
  | C a => simpa using const (α := ℕ) a
  | add p q hp hq => simpa using (comp nat_add (pair hp hq))
  | monomial n a h =>
    have := comp nat_mul (pair h (identity (α := ℕ)))
    refine of_funext this (fun x => ?_)
    simp [pow_succ, mul_assoc]


/-- A fold step that refuses to produce states whose encoding exceeds `B.eval |enc x|`. -/
def clampStep (B : Polynomial ℕ) (f : α → β → γ → β) (x : α) (b : β) (c : γ) : β :=
  if (enc (f x b c)).length ≤ B.eval (enc x).length then f x b c else b

theorem clampStep_fold_bound (B : Polynomial ℕ) (f : α → β → γ → β) (x : α) (cs : List γ) (b : β) :
    cs.foldl (clampStep B f x) b = b ∨
      (enc (cs.foldl (clampStep B f x) b)).length ≤ B.eval (enc x).length := by
  induction cs generalizing b with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    rcases ih (clampStep B f x b c) with h | h
    · simp only [List.foldl_cons]
      rw [h]; unfold clampStep
      split_ifs with h1
      · exact Or.inr h1
      · exact Or.inl rfl
    · exact Or.inr h

theorem clampStep_fold_eq (B : Polynomial ℕ) (f : α → β → γ → β) (x : α) (cs : List γ) (b : β)
    (hB : ∀ n ≤ cs.length, (enc ((cs.take n).foldl (f x) b)).length ≤ B.eval (enc x).length) :
    cs.foldl (clampStep B f x) b = cs.foldl (f x) b := by
  have key : ∀ n ≤ cs.length, (cs.take n).foldl (clampStep B f x) b = (cs.take n).foldl (f x) b := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hlt : n < cs.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
      have h2 := hB (n+1) hn
      rw [List.take_add_one, List.getElem?_eq_getElem hlt] at h2
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil] at h2
      simp only [clampStep, h2, if_true]
  have := key cs.length le_rfl
  simpa using this

/-- Generic fold with a context argument, provided every intermediate state is polynomially
bounded in the size of the input. -/
theorem foldl_ctx [Inhabited β] [Inhabited γ]
    {f : α → β → γ → β} {init : α → β} {as : α → List γ}
    (hf : Poly (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2)) (hinit : Poly init) (has : Poly as)
    (B : Polynomial ℕ)
    (hB : ∀ x, ∀ n ≤ (as x).length,
      (enc (((as x).take n).foldl (f x) (init x))).length ≤ B.eval (enc x).length) :
    Poly (fun x => (as x).foldl (f x) (init x)) := by
  open Polynomial in
  have hcl : Poly (fun p : (α × β) × γ => clampStep B f p.1.1 p.1.2 p.2) := by
    unfold clampStep
    refine ite_prop (nat_le_comp (comp (f := fun y : β => (enc y).length) enc_length hf)
      (comp (polynomial_eval B) (comp (f := fun y : α => (enc y).length) enc_length
        (comp fst fst)))) hf (comp snd fst)
  have hop : Poly (fun p : (α × β) × γ => (p.1.1, clampStep B f p.1.1 p.1.2 p.2)) :=
    pair (comp fst fst) hcl
  let op : (α × β) × γ → α × β := fun p => (p.1.1, clampStep B f p.1.1 p.1.2 p.2)
  have hfold : ∀ (cs : List γ) (s : α × β),
      cs.foldl (fun s c => op (s, c)) s = (s.1, cs.foldl (clampStep B f s.1) s.2) := by
    intro cs
    induction cs with
    | nil => intro s; rfl
    | cons c cs ih => intro s; simp only [List.foldl_cons]; rw [ih]
  let P : PolyProgram (encodePair (enc : α × β → List Bool) (enc : γ → List Bool)) enc op :=
    hop.program
  let F := P.listFold (default : γ) (3 * X + 1 + B) (by
    intro cs s pre suf he
    rw [hfold]
    have hx : (enc s.1).length ≤ (enc s).length := by
      show (enc s.1).length ≤ (encodePair enc enc s).length
      simp only [encodePair_length]; omega
    have hb : (enc s.2).length ≤ (enc s).length := by
      show (enc s.2).length ≤ (encodePair enc enc s).length
      simp only [encodePair_length]; omega
    have hs : (enc s).length ≤
        (encodePair (encodeList (enc : γ → List Bool)) (enc : α × β → List Bool) (cs, s)).length := by
      simp only [encodePair_length]; omega
    have hmono := polynomial_eval_mono B (hx.trans hs)
    change (encodePair enc enc (s.1, pre.foldl (clampStep B f s.1) s.2)).length ≤ _
    generalize (encodePair (encodeList (enc : γ → List Bool)) (enc : α × β → List Bool) (cs, s)).length = N at hs hmono ⊢
    simp only [encodePair_length, eval_add, eval_mul, eval_X, eval_one, eval_ofNat]
    rcases clampStep_fold_bound B f s.1 pre s.2 with h | h
    · rw [h]; omega
    · omega)
  have hF : Poly (fun y : List γ × (α × β) => y.1.foldl (fun s c => op (s, c)) y.2) := ⟨F⟩
  have := comp snd (comp hF (pair has (pair identity hinit)))
  refine of_funext this (fun x => ?_)
  simp only [id_eq]
  rw [hfold]
  exact clampStep_fold_eq B f x (as x) (init x) (hB x)



@[fun_prop] theorem list_all [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).all (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listAllWith default)⟩

@[fun_prop] theorem list_any [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).any (f x)) := by
  have h := comp bool_not (list_all (f := fun x b => !f x b) (comp bool_not hf) ha)
  refine of_funext h (fun x => ?_)
  generalize as x = l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.all_cons, List.any_cons, Bool.not_and, Bool.not_not, ih]

@[fun_prop] theorem list_headD_comp [Inhabited β] {xs : α → List β} {d : α → β}
    (hx : Poly xs) (hd : Poly d) : Poly (fun x => (xs x).headD (d x)) := by
  have h := ite (comp list_empty hx) hd (list_head_comp default hx)
  refine of_funext h (fun x => ?_)
  cases xs x <;> rfl

@[fun_prop] theorem list_getD_fn_comp (a0 : β) {xs : α → List β} {i : α → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun x => (xs x).getD (i x) a0) := by
  refine of_funext (list_getD_comp a0 hx hi) (fun x => ?_)
  simp [List.getD_eq_getElem?_getD]

@[fun_prop] theorem list_take [Inhabited β] : Poly (fun x : List β × ℕ => x.1.take x.2) :=
  ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem list_drop [Inhabited β] : Poly (fun x : List β × ℕ => x.1.drop x.2) :=
  ⟨PolyProgram.listDrop enc default⟩
@[fun_prop] theorem list_reverse [Inhabited β] : Poly (List.reverse : List β → List β) :=
  ⟨PolyProgram.listReverse enc default⟩
@[fun_prop] theorem list_take_comp [Inhabited β] {xs : α → List β} {n : α → ℕ}
    (hx : Poly xs) (hn : Poly n) : Poly (fun x => (xs x).take (n x)) :=
  comp (f := fun x : List β × ℕ => x.1.take x.2) list_take (pair hx hn)
@[fun_prop] theorem list_drop_comp [Inhabited β] {xs : α → List β} {n : α → ℕ}
    (hx : Poly xs) (hn : Poly n) : Poly (fun x => (xs x).drop (n x)) :=
  comp (f := fun x : List β × ℕ => x.1.drop x.2) list_drop (pair hx hn)
@[fun_prop] theorem list_reverse_comp [Inhabited β] {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).reverse) := comp list_reverse hx
@[fun_prop] theorem list_append_comp [Inhabited β] {xs ys : α → List β}
    (hx : Poly xs) (hy : Poly ys) : Poly (fun x => xs x ++ ys x) :=
  comp (f := fun x : List β × List β => x.1 ++ x.2) list_append (pair hx hy)
@[fun_prop] theorem list_cons_comp {a : α → β} {xs : α → List β}
    (ha : Poly a) (hx : Poly xs) : Poly (fun x => a x :: xs x) :=
  comp (f := fun x : β × List β => x.1 :: x.2) list_cons (pair ha hx)
@[fun_prop] theorem list_length_comp [Inhabited β] {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).length) := comp list_length hx
@[fun_prop] theorem list_tail_comp [Inhabited β] {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).tail) := comp list_tail hx
@[fun_prop] theorem list_isEmpty_comp {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).isEmpty) := comp list_empty hx
/-- `List.range` of the length of a (unary) list. -/
@[fun_prop] theorem list_range_length_comp [Inhabited β] {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => List.range (xs x).length) :=
  comp (f := fun xs : List β => List.range xs.length) list_indices hx

@[fun_prop] theorem list_eraseIdx [Inhabited β] : Poly (fun x : List β × ℕ => x.1.eraseIdx x.2) := by
  refine of_funext ⟨PolyProgram.listEraseIdx enc default⟩ (fun x => ?_)
  simp [List.eraseIdx_eq_take_drop_succ, List.tail_drop]
@[fun_prop] theorem list_eraseIdx_comp [Inhabited β] {xs : α → List β} {n : α → ℕ}
    (hx : Poly xs) (hn : Poly n) : Poly (fun x => (xs x).eraseIdx (n x)) :=
  comp (f := fun x : List β × ℕ => x.1.eraseIdx x.2) list_eraseIdx (pair hx hn)

@[fun_prop] theorem list_set [Inhabited β] : Poly (fun x : (List β × ℕ) × β => x.1.1.set x.1.2 x.2) := by
  have h : Poly (fun x : (List β × ℕ) × β =>
      if x.1.2 < x.1.1.length then x.1.1.take x.1.2 ++ x.2 :: x.1.1.drop (x.1.2 + 1) else x.1.1) := by
    refine ite_prop (nat_lt_comp (comp snd fst) (list_length_comp (comp fst fst)))
      (list_append_comp (list_take_comp (comp fst fst) (comp snd fst))
        (list_cons_comp snd (list_drop_comp (comp fst fst)
          (comp (f := fun x : ℕ × ℕ => x.1 + x.2) nat_add (pair (comp snd fst) (const 1)))))) (comp fst fst)
  refine of_funext h (fun x => ?_)
  rw [List.set_eq_take_append_cons_drop]
@[fun_prop] theorem list_set_comp [Inhabited β] {xs : α → List β} {n : α → ℕ} {a : α → β}
    (hx : Poly xs) (hn : Poly n) (ha : Poly a) : Poly (fun x => (xs x).set (n x) (a x)) :=
  comp (f := fun x : (List β × ℕ) × β => x.1.1.set x.1.2 x.2) list_set (pair (pair hx hn) ha)

/-- `List.replicate` with the count given in unary (as the length of a list). -/
@[fun_prop] theorem list_replicate_length [Inhabited β] [Inhabited γ] {xs : α → List β} {a : α → γ}
    (hx : Poly xs) (ha : Poly a) : Poly (fun x => List.replicate (xs x).length (a x)) := by
  have h := list_map (f := fun x (_ : β) => a x) (comp ha fst) hx
  refine of_funext h (fun x => ?_)
  simp [List.map_const']


@[fun_prop] theorem nat_beq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) := by
  refine of_funext (nat_eq_comp hf hg) (fun x => ?_)
  cases h : (f x == g x) <;> simp_all
@[fun_prop] theorem nat_bne_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x != g x) := by
  refine of_funext (comp bool_not (nat_beq_comp hf hg)) (fun x => ?_)
  simp [bne]
@[fun_prop] theorem bool_beq_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) := by
  refine of_funext (comp bool_not (bool_xor_comp hf hg)) (fun x => ?_)
  cases f x <;> cases g x <;> rfl
@[fun_prop] theorem nat_mul_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := comp (f := fun x : ℕ × ℕ => x.1 * x.2) nat_mul (pair hf hg)
@[fun_prop] theorem nat_add_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := comp (f := fun x : ℕ × ℕ => x.1 + x.2) nat_add (pair hf hg)
@[fun_prop] theorem nat_sub_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := comp (f := fun x : ℕ × ℕ => x.1 - x.2) nat_sub (pair hf hg)

@[fun_prop] theorem list_zip_comp [Inhabited β] [Inhabited γ] {xs : α → List β} {ys : α → List γ}
    (hx : Poly xs) (hy : Poly ys) : Poly (fun x => (xs x).zip (ys x)) :=
  comp (f := fun x : List β × List γ => x.1.zip x.2) list_zip (pair hx hy)

end OAI.MetricKMedian.Binary.Automatic.Poly

namespace OAI.MetricKMedian.Binary.Automatic
set_option linter.unusedSectionVars false
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

/-! ### Encoding lengths -/

theorem enc_pair_length (x : α × β) :
    (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length := encodePair_length _ _ _

theorem enc_nil_length : (enc ([] : List α)).length = 0 := rfl

theorem enc_cons_length (a : α) (l : List α) :
    (enc (a :: l)).length = 2 * (enc a).length + 1 + (enc l).length := EncodedList.cons_length _ _ _

theorem enc_bool_length (b : Bool) : (enc b).length = 1 := rfl

theorem enc_unit_length (b : Unit) : (enc b).length = 0 := rfl

theorem enc_list_length_le_of_forall (l : List α) (L : ℕ) (h : ∀ a ∈ l, (enc a).length ≤ L) :
    (enc l).length ≤ l.length * (2 * L + 1) := EncodedList.length_bound _ l L h

theorem enc_list_length_eq_of_forall (l : List α) (L : ℕ) (h : ∀ a ∈ l, (enc a).length = L) :
    (enc l).length = l.length * (2 * L + 1) := by
  induction l with
  | nil => simp [enc_nil_length]
  | cons a l ih =>
    rw [enc_cons_length, h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    simp only [List.length_cons]; ring

theorem enc_mem_length_le (l : List α) (a : α) (h : a ∈ l) : (enc a).length ≤ (enc l).length :=
  EncodedList.member_length _ l a h

theorem length_le_enc_length (l : List α) : l.length ≤ (enc l).length := EncodedList.length_le _ l

theorem enc_listBool_length (l : List Bool) : (enc l).length = 3 * l.length := by
  rw [enc_list_length_eq_of_forall l 1 (fun _ _ => rfl)]; ring

theorem enc_listUnit_length (l : List Unit) : (enc l).length = l.length := by
  rw [enc_list_length_eq_of_forall l 0 (fun _ _ => rfl)]; ring

end OAI.MetricKMedian.Binary.Automatic

namespace PfaffianRecognition.CoRP.PolyLib

/-- A fold either returns its initial value or a value produced by a step. -/
theorem foldl_eq_or {β γ : Type} (g : β → γ → β) (Q : β → Prop) (hg : ∀ b c, Q (g b c))
    (cs : List γ) (b : β) : cs.foldl g b = b ∨ Q (cs.foldl g b) := by
  induction cs generalizing b with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    rcases ih (g b c) with h | h
    · exact Or.inr (by simp only [List.foldl_cons, h]; exact hg b c)
    · exact Or.inr h

/-- Fold invariant. -/
theorem foldl_invariant {β γ : Type} (g : β → γ → β) (Q : β → Prop) (hg : ∀ b c, Q b → Q (g b c))
    (cs : List γ) (b : β) (hb : Q b) : Q (cs.foldl g b) := by
  induction cs generalizing b with
  | nil => exact hb
  | cons c cs ih => exact ih _ (hg b c hb)

end PfaffianRecognition.CoRP.PolyLib

namespace PfaffianRecognition.CoRP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Fold with a context argument, provided every intermediate state is polynomially bounded. -/
theorem poly_foldl_ctx {α β γ : Type} [Coding α] [Coding β] [Coding γ] [Inhabited β] [Inhabited γ]
    {f : α → β → γ → β} {init : α → β} {as : α → List γ}
    (hf : Poly (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2)) (hinit : Poly init) (has : Poly as)
    (B : Polynomial ℕ)
    (hB : ∀ x, ∀ n ≤ (as x).length,
      (enc (((as x).take n).foldl (f x) (init x))).length ≤ B.eval (enc x).length) :
    Poly (fun x => (as x).foldl (f x) (init x)) :=
  Poly.foldl_ctx hf hinit has B hB

theorem poly_range_two_mul {α : Type} [Coding α] {u : α → List Unit} (hu : Poly u) :
    Poly (fun x => List.range (2 * (u x).length)) := by
  have h := Poly.list_range_length_comp (Poly.list_append_comp hu hu)
  refine Poly.of_funext h (fun x => ?_)
  simp [two_mul]

theorem poly_gfZero : Poly (fun u : List Unit => gfZero u.length) := by
  unfold gfZero
  exact Poly.list_map (f := fun _ _ => false) (Automatic.Poly.const false) (poly_range_two_mul Poly.identity)

theorem poly_gfOne : Poly (fun u : List Unit => gfOne u.length) := by
  unfold gfOne
  exact Poly.list_map (f := fun _ i => decide (i = 0)) (by fun_prop) (poly_range_two_mul Poly.identity)

theorem poly_gfAdd : Poly (fun p : List Unit × (List Bool × List Bool) => gfAdd p.1.length p.2.1 p.2.2) := by
  unfold gfAdd
  exact Poly.list_map (f := fun (p : List Unit × (List Bool × List Bool)) (i : ℕ) => xor (p.2.1.getD i false) (p.2.2.getD i false)) (by fun_prop)
    (poly_range_two_mul Poly.fst)

theorem poly_gfIsZero : Poly (fun p : List Unit × List Bool => gfIsZero p.1.length p.2) := by
  unfold gfIsZero
  exact Poly.list_all (f := fun (p : List Unit × List Bool) (i : ℕ) => !p.2.getD i false) (by fun_prop) (poly_range_two_mul Poly.fst)

theorem poly_gfIndexPairs {α : Type} [Coding α] {u : α → List Unit} (hu : Poly u) :
    Poly (fun x => gfIndexPairs (u x).length) := by
  unfold gfIndexPairs
  refine Poly.list_flatMap (f := fun (x : α) (j : ℕ) => (List.range (2 * (u x).length)).map (fun l => (j, l)))
    ?_ (poly_range_two_mul hu)
  exact Poly.list_map (f := fun (y : α × ℕ) (l : ℕ) => (y.2, l)) (by fun_prop)
    (poly_range_two_mul (Poly.comp hu Poly.fst))

theorem poly_gfMul : Poly (fun p : List Unit × (List Bool × List Bool) => gfMul p.1.length p.2.1 p.2.2) := by
  unfold gfMul
  refine Poly.list_map (f := fun (p : List Unit × (List Bool × List Bool)) (i : ℕ) =>
    (((gfIndexPairs p.1.length).filter (fun jl => p.2.1.getD jl.1 false && p.2.2.getD jl.2 false &&
      ((jl.1 + jl.2) % (3 * p.1.length) == i ||
        (jl.1 + jl.2) % (3 * p.1.length) == (if i < p.1.length then i + 2 * p.1.length else i + p.1.length)))).length % 2 == 1)) ?_
    (poly_range_two_mul Poly.fst)
  refine Poly.nat_beq_comp (Poly.nat_mod_comp (Poly.list_length_comp (Poly.list_filter
    (f := fun (y : (List Unit × (List Bool × List Bool)) × ℕ) (jl : ℕ × ℕ) =>
      y.1.2.1.getD jl.1 false && y.1.2.2.getD jl.2 false &&
      ((jl.1 + jl.2) % (3 * y.1.1.length) == y.2 ||
        (jl.1 + jl.2) % (3 * y.1.1.length) ==
          (if y.2 < y.1.1.length then y.2 + 2 * y.1.1.length else y.2 + y.1.1.length))) ?_
    (poly_gfIndexPairs (Poly.comp Poly.fst Poly.fst)))) (Automatic.Poly.const 2)) (Automatic.Poly.const 1)
  fun_prop

theorem gfZero_length (m : ℕ) : (gfZero m).length = 2 * m := by simp [gfZero]
theorem gfOne_length (m : ℕ) : (gfOne m).length = 2 * m := by simp [gfOne]
theorem gfAdd_length (m : ℕ) (a b : List Bool) : (gfAdd m a b).length = 2 * m := by simp [gfAdd]
theorem gfMul_length (m : ℕ) (a b : List Bool) : (gfMul m a b).length = 2 * m := by simp [gfMul]

section comp
variable {α : Type} [Coding α] {u : α → List Unit} {a b : α → List Bool}

@[fun_prop] theorem poly_gfZero_comp (hu : Poly u) : Poly (fun x => gfZero (u x).length) :=
  Poly.comp (f := fun v : List Unit => gfZero v.length) (g := u) poly_gfZero hu
@[fun_prop] theorem poly_gfOne_comp (hu : Poly u) : Poly (fun x => gfOne (u x).length) :=
  Poly.comp (f := fun v : List Unit => gfOne v.length) (g := u) poly_gfOne hu
@[fun_prop] theorem poly_gfAdd_comp (hu : Poly u) (ha : Poly a) (hb : Poly b) :
    Poly (fun x => gfAdd (u x).length (a x) (b x)) :=
  Poly.comp (f := fun p : List Unit × (List Bool × List Bool) => gfAdd p.1.length p.2.1 p.2.2)
    (g := fun x => (u x, (a x, b x))) poly_gfAdd (Poly.pair hu (Poly.pair ha hb))
@[fun_prop] theorem poly_gfMul_comp (hu : Poly u) (ha : Poly a) (hb : Poly b) :
    Poly (fun x => gfMul (u x).length (a x) (b x)) :=
  Poly.comp (f := fun p : List Unit × (List Bool × List Bool) => gfMul p.1.length p.2.1 p.2.2)
    (g := fun x => (u x, (a x, b x))) poly_gfMul (Poly.pair hu (Poly.pair ha hb))
@[fun_prop] theorem poly_gfIsZero_comp (hu : Poly u) (ha : Poly a) :
    Poly (fun x => gfIsZero (u x).length (a x)) :=
  Poly.comp (f := fun p : List Unit × List Bool => gfIsZero p.1.length p.2)
    (g := fun x => (u x, a x)) poly_gfIsZero (Poly.pair hu ha)
end comp

theorem poly_gfInv : Poly (fun p : List Unit × List Bool => gfInv p.1.length p.2) := by
  unfold gfInv
  have hinit : Poly (fun p : List Unit × List Bool => (p.2, gfOne p.1.length)) := by fun_prop
  have has : Poly (fun p : List Unit × List Bool => List.range (2 * p.1.length - 1)) := by
    refine Poly.of_funext (Poly.list_range_length_comp (Poly.list_tail_comp
      (Poly.list_append_comp (Poly.fst (β := List Bool)) Poly.fst))) (fun x => ?_)
    simp [two_mul]
  have hf : Poly (fun q : ((List Unit × List Bool) × (List Bool × List Bool)) × ℕ =>
      (gfMul q.1.1.1.length q.1.2.1 q.1.2.1,
        gfMul q.1.1.1.length q.1.2.2 (gfMul q.1.1.1.length q.1.2.1 q.1.2.1))) := by fun_prop
  refine Poly.snd.comp (Poly.foldl_ctx (f := fun (p : List Unit × List Bool) (st : List Bool × List Bool) (_ : ℕ) =>
      (gfMul p.1.length st.1 st.1, gfMul p.1.length st.2 (gfMul p.1.length st.1 st.1))) hf hinit has
    (9 * Polynomial.X) ?_)
  intro p n _
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hL : (enc p).length = 2 * p.1.length + 1 + 3 * p.2.length := by
    rw [enc_pair_length, enc_listUnit_length, enc_listBool_length]
  rcases PolyLib.foldl_eq_or (fun (st : List Bool × List Bool) (_ : ℕ) =>
      (gfMul p.1.length st.1 st.1, gfMul p.1.length st.2 (gfMul p.1.length st.1 st.1)))
      (fun st : List Bool × List Bool => st.1.length = 2 * p.1.length ∧
      st.2.length = 2 * p.1.length) (fun st _ => ⟨gfMul_length _ _ _, gfMul_length _ _ _⟩)
      ((List.range (2 * p.1.length - 1)).take n) (p.2, gfOne p.1.length) with h | h
  · rw [h, enc_pair_length, enc_listBool_length, enc_listBool_length, hL]
    simp only [gfOne_length]; omega
  · rw [enc_pair_length, enc_listBool_length, enc_listBool_length, h.1, h.2, hL]; omega

theorem poly_listSum :
    Poly (fun p : List Unit × List (List Bool) => listSum (gfOps p.1.length) p.2) := by
  show Poly (fun p : List Unit × List (List Bool) => p.2.foldl (gfAdd p.1.length) (gfZero p.1.length))
  refine Poly.foldl_ctx (f := fun (p : List Unit × List (List Bool)) (b : List Bool) (a : List Bool) =>
      gfAdd p.1.length b a) (by fun_prop) (by fun_prop) Poly.snd (3 * Polynomial.X) ?_
  intro p n _
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hL : 2 * p.1.length ≤ (enc p).length := by
    rw [enc_pair_length, enc_listUnit_length]; omega
  rcases PolyLib.foldl_eq_or (gfAdd p.1.length) (fun st : List Bool => st.length = 2 * p.1.length)
      (fun st _ => gfAdd_length _ _ _) (p.2.take n) (gfZero p.1.length) with h | h
  · rw [h, enc_listBool_length, gfZero_length]; omega
  · rw [enc_listBool_length, h]; omega


@[fun_prop] theorem poly_gfInv_comp {α : Type} [Coding α] {u : α → List Unit} {a : α → List Bool}
    (hu : Poly u) (ha : Poly a) :
    Poly (fun x => gfInv (u x).length (a x)) :=
  Poly.comp (f := fun p : List Unit × List Bool => gfInv p.1.length p.2)
    (g := fun x => (u x, a x)) poly_gfInv (Poly.pair hu ha)

section detAlg
variable {α : Type} [Coding α] {u : α → List Unit}

@[fun_prop] theorem poly_pivotIdx_gf_comp {rows : α → List (List (List Bool))} (hu : Poly u) (hr : Poly rows) :
    Poly (fun x => pivotIdx (gfOps (u x).length) (rows x)) := by
  unfold pivotIdx
  exact Poly.list_findIdx (f := fun x (r : List (List Bool)) =>
    !gfIsZero (u x).length (r.headD (gfZero (u x).length))) (by fun_prop) hr

@[fun_prop] theorem poly_elimRow_gf_comp {pinv : α → List Bool} {piv row : α → List (List Bool)}
    (hu : Poly u) (hp : Poly pinv) (hpiv : Poly piv) (hrow : Poly row) :
    Poly (fun x => elimRow (gfOps (u x).length) (pinv x) (piv x) (row x)) := by
  unfold elimRow
  exact Poly.list_map (f := fun x (ab : List Bool × List Bool) =>
    gfAdd (u x).length ab.1 (gfMul (u x).length (gfMul (u x).length
      ((row x).headD (gfZero (u x).length)) (pinv x)) ab.2)) (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_elimStep_gf_comp {st : α → List (List (List Bool)) × List Bool}
    (hu : Poly u) (hst : Poly st) :
    Poly (fun x => elimStep (gfOps (u x).length) (st x)) := by
  unfold elimStep
  have hrows : Poly (fun x => (st x).1) := Poly.comp Poly.fst hst
  have hk := poly_pivotIdx_gf_comp hu hrows
  have hmap : Poly (fun x => ((st x).1.eraseIdx (pivotIdx (gfOps (u x).length) (st x).1)).map
      (elimRow (gfOps (u x).length)
        (gfInv (u x).length (((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []).headD
          (gfZero (u x).length)))
        ((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []))) := by
    refine Poly.list_map (f := fun x (r : List (List Bool)) => elimRow (gfOps (u x).length)
        (gfInv (u x).length (((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []).headD
          (gfZero (u x).length)))
        ((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []) r) ?_ (by fun_prop)
    have hu' : Poly (fun y : α × List (List Bool) => u y.1) := Poly.comp (f := u) (g := Prod.fst) hu Poly.fst
    have hk' : Poly (fun y : α × List (List Bool) => pivotIdx (gfOps (u y.1).length) (st y.1).1) :=
      Poly.comp (f := fun x => pivotIdx (gfOps (u x).length) (st x).1) (g := Prod.fst) hk Poly.fst
    have hrows' : Poly (fun y : α × List (List Bool) => (st y.1).1) :=
      Poly.comp (f := fun x => (st x).1) (g := Prod.fst) hrows Poly.fst
    exact poly_elimRow_gf_comp hu' (by fun_prop) (by fun_prop) Poly.snd
  have hacc : Poly (fun x => gfMul (u x).length (st x).2
      (if pivotIdx (gfOps (u x).length) (st x).1 % 2 = 0 then
        ((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []).headD (gfZero (u x).length)
      else ((st x).1.getD (pivotIdx (gfOps (u x).length) (st x).1) []).headD (gfZero (u x).length))) := by
    fun_prop
  exact Poly.ite (Poly.list_isEmpty_comp hrows) hst
    (Poly.ite_prop (Poly.nat_lt_comp hk (Poly.list_length_comp hrows)) (Poly.pair hmap hacc)
      (Poly.pair (Automatic.Poly.const []) (poly_gfZero_comp hu)))

end detAlg

theorem elimRow_length_le {β : Type} (F : FieldOps β) (pinv : β) (piv row : List β) :
    (elimRow F pinv piv row).length ≤ row.length := by
  simp only [elimRow, List.length_map, List.length_zip, List.length_tail]; omega

theorem mem_elimRow_gf_length (m : ℕ) (pinv : List Bool) (piv row : List (List Bool)) (e : List Bool)
    (h : e ∈ elimRow (gfOps m) pinv piv row) : e.length = 2 * m := by
  simp only [elimRow, List.mem_map] at h
  obtain ⟨ab, _, rfl⟩ := h
  exact gfAdd_length _ _ _

/-- Shape invariant of the Gaussian-elimination state (before entries are normalized). -/
def DetShape (m L : ℕ) (st : List (List (List Bool)) × List Bool) : Prop :=
  st.1.length ≤ L ∧ (∀ r ∈ st.1, r.length ≤ L) ∧ st.2.length = 2 * m

/-- Shape invariant after at least one elimination step: all entries have length `2m`. -/
def DetShape' (m L : ℕ) (st : List (List (List Bool)) × List Bool) : Prop :=
  DetShape m L st ∧ ∀ r ∈ st.1, ∀ e ∈ r, e.length = 2 * m

theorem elimStep_gf_shape (m L : ℕ) (st : List (List (List Bool)) × List Bool)
    (h : DetShape m L st) : DetShape' m L (elimStep (gfOps m) st) := by
  unfold elimStep
  by_cases h1 : st.1.isEmpty = true
  · rw [if_pos h1]
    refine ⟨h, ?_⟩
    rw [List.isEmpty_iff.mp h1]; simp
  rw [if_neg h1]
  by_cases h2 : pivotIdx (gfOps m) st.1 < st.1.length
  · rw [if_pos h2]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [List.length_map]
      exact (List.length_eraseIdx_le _ _).trans h.1
    · intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := hr
      exact (elimRow_length_le _ _ _ _).trans (h.2.1 r0 (List.mem_of_mem_eraseIdx hr0))
    · exact gfMul_length _ _ _
    · intro r hr e he
      simp only [List.mem_map] at hr
      obtain ⟨r0, _, rfl⟩ := hr
      exact mem_elimRow_gf_length m _ _ _ e he
  · rw [if_neg h2]
    exact ⟨⟨by simp, by simp, gfZero_length m⟩, by simp⟩

theorem enc_detShape'_le (m L : ℕ) (st : List (List (List Bool)) × List Bool)
    (h : DetShape' m L st) (hm : 2 * m ≤ L) : (enc st).length ≤ 64 * (L + 1) ^ 3 := by
  have he : ∀ r ∈ st.1, ∀ e ∈ r, (enc e).length ≤ 3 * L := by
    intro r hr e hre
    rw [enc_listBool_length, h.2 r hr e hre]; omega
  have hr : ∀ r ∈ st.1, (enc r).length ≤ L * (2 * (3 * L) + 1) := fun r hr =>
    (enc_list_length_le_of_forall r _ (he r hr)).trans (Nat.mul_le_mul_right _ (h.1.2.1 r hr))
  have hrows : (enc st.1).length ≤ L * (2 * (L * (2 * (3 * L) + 1)) + 1) :=
    (enc_list_length_le_of_forall _ _ hr).trans (Nat.mul_le_mul_right _ h.1.1)
  rw [enc_pair_length, enc_listBool_length, h.1.2.2]
  nlinarith

theorem poly_detAlg :
    Poly (fun p : List Unit × List (List (List Bool)) => detAlg (gfOps p.1.length) p.2) := by
  show Poly (fun p : List Unit × List (List (List Bool)) =>
    ((List.range p.2.length).foldl (fun st _ => elimStep (gfOps p.1.length) st)
      (p.2, gfOne p.1.length)).2)
  have hf : Poly (fun q : ((List Unit × List (List (List Bool))) × (List (List (List Bool)) × List Bool)) × ℕ =>
      elimStep (gfOps q.1.1.1.length) q.1.2) :=
    poly_elimStep_gf_comp
      (u := fun (q : ((List Unit × List (List (List Bool))) × (List (List (List Bool)) × List Bool)) × ℕ) => q.1.1.1) (by fun_prop) (by fun_prop)
  refine Poly.snd.comp (Poly.foldl_ctx
    (f := fun (p : List Unit × List (List (List Bool))) (st : List (List (List Bool)) × List Bool) (_ : ℕ) =>
      elimStep (gfOps p.1.length) st) hf (by fun_prop) (by fun_prop) (64 * (Polynomial.X + 1) ^ 3) ?_)
  intro p n _
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one]
  set L := (enc p).length with hLdef
  have hL : (enc p).length = 2 * p.1.length + 1 + (enc p.2).length := by
    rw [enc_pair_length, enc_listUnit_length]
  have hm : 2 * p.1.length ≤ L := by omega
  have hM : (enc p.2).length ≤ L := by omega
  have hinit : DetShape p.1.length L (p.2, gfOne p.1.length) := by
    refine ⟨(length_le_enc_length _).trans hM, fun r hr => ?_, gfOne_length _⟩
    exact ((length_le_enc_length r).trans (enc_mem_length_le _ _ hr)).trans hM
  have hinv := PolyLib.foldl_invariant (fun st (_ : ℕ) => elimStep (gfOps p.1.length) st)
    (fun st => st = (p.2, gfOne p.1.length) ∨ DetShape' p.1.length L st)
    (fun st _ hst => by
      right
      rcases hst with rfl | hst
      · exact elimStep_gf_shape _ _ _ hinit
      · exact elimStep_gf_shape _ _ _ hst.1)
    ((List.range p.2.length).take n) (p.2, gfOne p.1.length) (Or.inl rfl)
  rcases hinv with h | h
  · rw [h, enc_pair_length, enc_listBool_length, gfOne_length]
    dsimp only
    have : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  · exact enc_detShape'_le _ _ _ h hm


/-! ### Linear systems over `𝔽₂` -/

section solve
variable {α : Type} [Coding α]

@[fun_prop] theorem poly_addEqn_comp {e f : α → Eqn} (he : Poly e) (hf : Poly f) :
    Poly (fun x => addEqn (e x) (f x)) := by
  unfold addEqn
  have hlist : Poly (fun x => if (e x).1.length ≤ (f x).1.length then (f x).1 else (e x).1) := by
    fun_prop
  have hr : Poly (fun x => List.range (max (e x).1.length (f x).1.length)) := by
    refine Poly.of_funext (Poly.list_range_length_comp hlist) (fun x => ?_)
    split_ifs with h
    · rw [max_eq_right h]
    · rw [max_eq_left (by omega)]
  refine Poly.pair (Poly.list_map (f := fun x (i : ℕ) => xor ((e x).1.getD i false) ((f x).1.getD i false))
    (by fun_prop) hr) (by fun_prop)

@[fun_prop] theorem poly_f2Forward_comp {st : α → List Eqn × List Eqn} {j : α → ℕ}
    (hst : Poly st) (hj : Poly j) : Poly (fun x => f2Forward (st x) (j x)) := by
  unfold f2Forward
  have hk : Poly (fun x => (st x).1.findIdx (fun e => e.1.getD (j x) false)) :=
    Poly.list_findIdx (f := fun x (e : Eqn) => e.1.getD (j x) false) (by fun_prop) (by fun_prop)
  have hmap : Poly (fun x => ((st x).1.eraseIdx ((st x).1.findIdx (fun e => e.1.getD (j x) false))).map
      (fun e => if e.1.getD (j x) false then
        addEqn e ((st x).1.getD ((st x).1.findIdx (fun e => e.1.getD (j x) false)) ([], false)) else e)) := by
    refine Poly.list_map (f := fun x (e : Eqn) => if e.1.getD (j x) false then
        addEqn e ((st x).1.getD ((st x).1.findIdx (fun e => e.1.getD (j x) false)) ([], false)) else e)
      ?_ (Poly.list_eraseIdx_comp (xs := fun x => (st x).1) (by fun_prop) hk)
    have hk' : Poly (fun y : α × Eqn => (st y.1).1.findIdx (fun e => e.1.getD (j y.1) false)) :=
      Poly.comp (f := fun x => (st x).1.findIdx (fun e => e.1.getD (j x) false)) (g := Prod.fst) hk Poly.fst
    have hst' : Poly (fun y : α × Eqn => st y.1) := Poly.comp (f := st) (g := Prod.fst) hst Poly.fst
    fun_prop
  refine Poly.ite_prop (Poly.nat_lt_comp hk (by fun_prop)) (Poly.pair hmap ?_) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_f2Back_comp [Inhabited α] {pv : α → List Eqn} {xs : α → List Bool} {j : α → ℕ}
    (hpv : Poly pv) (hxs : Poly xs) (hj : Poly j) : Poly (fun x => f2Back (pv x) (xs x) (j x)) := by
  unfold f2Back
  have hp : Poly (fun x => (pv x).getD (j x) ([], false)) := by fun_prop
  refine Poly.list_set_comp hxs hj (Poly.bool_xor_comp (by fun_prop) (Poly.nat_beq_comp
    (Poly.nat_mod_comp (Poly.list_length_comp (Poly.list_filter
      (f := fun x (l : ℕ) => l != j x && ((pv x).getD (j x) ([], false)).1.getD l false && (xs x).getD l false)
      ?_ (by fun_prop))) (Automatic.Poly.const 2)) (Automatic.Poly.const 1)))
  have hp' : Poly (fun y : α × ℕ => (pv y.1).getD (j y.1) ([], false)) :=
    Poly.comp (f := fun x => (pv x).getD (j x) ([], false)) (g := Prod.fst) hp Poly.fst
  fun_prop

end solve

theorem addEqn_length (e f : Eqn) : (addEqn e f).1.length = max e.1.length f.1.length := by
  simp [addEqn]

/-- Size invariant of the forward-elimination state. -/
def FwdInv (C R : ℕ) (st : List Eqn × List Eqn) : Prop :=
  st.1.length ≤ R ∧ ∀ e ∈ st.1 ++ st.2, e.1.length ≤ C

theorem f2Forward_inv (C R : ℕ) (st : List Eqn × List Eqn) (j : ℕ) (h : FwdInv C R st) :
    FwdInv C R (f2Forward st j) ∧ (f2Forward st j).2.length = st.2.length + 1 := by
  unfold f2Forward
  split_ifs with hk
  · set k := st.1.findIdx (fun e => e.1.getD j false)
    have hpiv : st.1.getD k ([], false) ∈ st.1 := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hC : ∀ e ∈ st.1, e.1.length ≤ C := fun e he => h.2 e (List.mem_append_left _ he)
    refine ⟨⟨?_, ?_⟩, by simp⟩
    · simp only [List.length_map]
      exact (List.length_eraseIdx_le _ _).trans h.1
    · intro e he
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
      rcases he with ⟨e0, he0, rfl⟩ | he | rfl
      · have he0' := List.mem_of_mem_eraseIdx he0
        split_ifs
        · rw [addEqn_length]; exact max_le (hC e0 he0') (hC _ hpiv)
        · exact hC e0 he0'
      · exact h.2 e (List.mem_append_right _ he)
      · exact hC _ hpiv
  · refine ⟨⟨h.1, ?_⟩, by simp⟩
    intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | he | rfl
    · exact h.2 e (List.mem_append_left _ he)
    · exact h.2 e (List.mem_append_right _ he)
    · simp

theorem fold_f2Forward_inv (C R : ℕ) (cs : List ℕ) (st : List Eqn × List Eqn) (h : FwdInv C R st) :
    FwdInv C R (cs.foldl f2Forward st) ∧ (cs.foldl f2Forward st).2.length = st.2.length + cs.length := by
  induction cs generalizing st with
  | nil => exact ⟨h, rfl⟩
  | cons c cs ih =>
    have h1 := f2Forward_inv C R st c h
    have h2 := ih _ h1.1
    refine ⟨h2.1, ?_⟩
    simp only [List.foldl_cons, h2.2, h1.2, List.length_cons]; omega

theorem enc_eqn_length (e : Eqn) : (enc e).length = 6 * e.1.length + 2 := by
  rw [enc_pair_length, enc_listBool_length, enc_bool_length]; ring

theorem poly_f2ForwardFold :
    Poly (fun p : List Unit × List Eqn => (List.range p.1.length).foldl f2Forward (p.2, [])) := by
  refine Poly.foldl_ctx (f := fun (_ : List Unit × List Eqn) (st : List Eqn × List Eqn) (j : ℕ) =>
    f2Forward st j) (by fun_prop) (by fun_prop) (by fun_prop) (64 * (Polynomial.X + 1) ^ 2) ?_
  intro p n hn
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one]
  set L := (enc p).length with hLdef
  have hL : (enc p).length = 2 * p.1.length + 1 + (enc p.2).length := by
    rw [enc_pair_length, enc_listUnit_length]
  have hinit : FwdInv L L (p.2, []) := by
    refine ⟨(length_le_enc_length p.2).trans (by omega), fun e he => ?_⟩
    simp only [List.append_nil] at he
    have h1 := enc_mem_length_le _ _ he
    have h2 := length_le_enc_length e.1
    have h3 := enc_eqn_length e
    omega
  have hinv := fold_f2Forward_inv L L ((List.range p.1.length).take n) (p.2, []) hinit
  have hlen : ((List.range p.1.length).take n).length ≤ L := by
    simp only [List.length_take, List.length_range]; omega
  set st := ((List.range p.1.length).take n).foldl f2Forward (p.2, [])
  have hC : ∀ e ∈ st.1 ++ st.2, (enc e).length ≤ 6 * L + 2 := fun e he => by
    rw [enc_eqn_length]; have := hinv.1.2 e he; omega
  have h1 : (enc st.1).length ≤ L * (2 * (6 * L + 2) + 1) :=
    (enc_list_length_le_of_forall _ _ (fun e he => hC e (List.mem_append_left _ he))).trans
      (Nat.mul_le_mul_right _ hinv.1.1)
  have h2 : (enc st.2).length ≤ L * (2 * (6 * L + 2) + 1) :=
    (enc_list_length_le_of_forall _ _ (fun e he => hC e (List.mem_append_right _ he))).trans
      (Nat.mul_le_mul_right _ (by rw [hinv.2]; simpa using hlen))
  rw [enc_pair_length]
  nlinarith

theorem f2Back_length (pv : List Eqn) (x : List Bool) (j : ℕ) : (f2Back pv x j).length = x.length := by
  simp [f2Back]

theorem poly_f2BackFold :
    Poly (fun y : List Unit × List Eqn =>
      (List.range y.1.length).reverse.foldl (f2Back y.2) (List.replicate y.1.length false)) := by
  refine Poly.foldl_ctx (f := fun (y : List Unit × List Eqn) (x : List Bool) (j : ℕ) => f2Back y.2 x j)
    (by fun_prop) (Poly.list_replicate_length Poly.fst (Automatic.Poly.const false)) (by fun_prop)
    (3 * Polynomial.X) ?_
  intro y n _
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hL : y.1.length ≤ (enc y).length := by
    rw [enc_pair_length, enc_listUnit_length]; omega
  have hinv := PolyLib.foldl_invariant (f2Back y.2) (fun x : List Bool => x.length = y.1.length)
    (fun x j hx => by simp only [f2Back_length, hx]) ((List.range y.1.length).reverse.take n)
    (List.replicate y.1.length false) (by simp)
  rw [enc_listBool_length, hinv]; omega

theorem poly_solveF2 : Poly (fun p : List Unit × List Eqn => solveF2 p.1.length p.2) := by
  unfold solveF2
  have hF := poly_f2ForwardFold
  have hB := poly_f2BackFold
  refine Poly.pair (Poly.list_all (f := fun _ (e : Eqn) => !e.2) (by fun_prop)
    (Poly.comp (f := fun st : List Eqn × List Eqn => st.1) Poly.fst hF)) ?_
  exact Poly.comp (f := fun y : List Unit × List Eqn =>
      (List.range y.1.length).reverse.foldl (f2Back y.2) (List.replicate y.1.length false))
    (g := fun p : List Unit × List Eqn => (p.1, ((List.range p.1.length).foldl f2Forward (p.2, [])).2))
    hB (Poly.pair Poly.fst (Poly.comp (f := Prod.snd) Poly.snd hF))

end PfaffianRecognition.CoRP

-- `polyProgram_pfAlg` (the whole algorithm) is handled separately.


namespace PfaffianRecognition.CoRP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic



/-! Generic helpers -/

namespace PA
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem of_eq {f g : α → β} (h : Poly f) (e : ∀ x, f x = g x) : Poly g := by
  have : f = g := funext e
  exact this ▸ h

@[fun_prop] theorem nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem bool_xor : Poly (fun x : Bool × Bool => xor x.1 x.2) := ⟨PolyProgram.boolXor⟩
@[fun_prop] theorem nat_mod_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) := Poly.comp (f := fun x : ℕ × ℕ => x.1 % x.2) nat_mod (Poly.pair hf hg)
@[fun_prop] theorem bool_xor_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xor (f x) (g x)) := Poly.comp (f := fun x : Bool × Bool => xor x.1 x.2) bool_xor (Poly.pair hf hg)
@[fun_prop] theorem bool_and_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)
@[fun_prop] theorem bool_or_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x || g x) := Poly.comp Poly.bool_or (Poly.pair hf hg)
@[fun_prop] theorem bool_not_comp {f : α → Bool} (hf : Poly f) :
    Poly (fun x => !f x) := Poly.comp Poly.bool_not hf

@[fun_prop] theorem nat_beq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) :=
  of_eq (Poly.nat_eq_comp hf hg) (fun x => by simp [beq_eq_decide])

@[fun_prop] theorem bool_beq_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) :=
  of_eq (g := fun x => f x == g x) (Poly.ite hf hg (bool_not_comp hg)) (fun x => by
    cases f x <;> cases g x <;> rfl)

@[fun_prop] theorem pair_beq_comp {f g : α → ℕ × ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) := by
  have h : Poly (fun x => (f x).1 == (g x).1 && (f x).2 == (g x).2) := by fun_prop
  refine of_eq h (fun x => ?_)
  rcases f x with ⟨a, b⟩; rcases g x with ⟨c, d⟩
  simp [beq_eq_decide, Prod.ext_iff]

@[fun_prop] theorem nat_min_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => min (f x) (g x)) := by
  have h : Poly (fun x => if f x ≤ g x then f x else g x) := Poly.ite_prop (by fun_prop) hf hg
  exact of_eq h (fun x => Nat.min_def.symm)

@[fun_prop] theorem nat_max_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => max (f x) (g x)) := by
  have h : Poly (fun x => if f x ≤ g x then g x else f x) := Poly.ite_prop (by fun_prop) hg hf
  exact of_eq h (fun x => Nat.max_def.symm)

@[fun_prop] theorem list_take_comp [Inhabited β] {l : α → List β} {n : α → ℕ} (hl : Poly l) (hn : Poly n) :
    Poly (fun x => (l x).take (n x)) :=
  Poly.comp (f := fun x : List β × ℕ => x.1.take x.2) ⟨PolyProgram.listTake enc default⟩ (Poly.pair hl hn)

@[fun_prop] theorem list_drop_comp [Inhabited β] {l : α → List β} {n : α → ℕ} (hl : Poly l) (hn : Poly n) :
    Poly (fun x => (l x).drop (n x)) :=
  Poly.comp (f := fun x : List β × ℕ => x.1.drop x.2) ⟨PolyProgram.listDrop enc default⟩ (Poly.pair hl hn)

@[fun_prop] theorem list_getD_comp' [Inhabited β] {l : α → List β} {n : α → ℕ} {d : α → β}
    (hl : Poly l) (hn : Poly n) (hd : Poly d) :
    Poly (fun x => (l x).getD (n x) (d x)) := by
  have h : Poly (fun x => if n x < (l x).length then (l x)[n x]?.getD default else d x) :=
    Poly.ite_prop (Poly.nat_lt_comp hn (Poly.comp Poly.list_length hl))
      (Poly.list_getD_comp default hl hn) hd
  refine of_eq h (fun x => ?_)
  by_cases hc : n x < (l x).length
  · simp [hc, List.getD_eq_getElem?_getD]
  · simp [hc, List.getD_eq_getElem?_getD]

@[fun_prop] theorem list_length_comp [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => (l x).length) := Poly.comp Poly.list_length hl

@[fun_prop] theorem list_isEmpty_comp {l : α → List β} (hl : Poly l) :
    Poly (fun x => (l x).isEmpty) := Poly.comp Poly.list_empty hl

@[fun_prop] theorem list_append_comp [Inhabited β] {l l' : α → List β} (hl : Poly l) (hl' : Poly l') :
    Poly (fun x => l x ++ l' x) := Poly.comp Poly.list_append (Poly.pair hl hl')

@[fun_prop] theorem list_cons_comp {a : α → β} {l : α → List β} (ha : Poly a) (hl : Poly l) :
    Poly (fun x => a x :: l x) := Poly.comp Poly.list_cons (Poly.pair ha hl)

@[fun_prop] theorem list_zip_comp [Inhabited β] [Inhabited γ] {l : α → List β} {l' : α → List γ}
    (hl : Poly l) (hl' : Poly l') : Poly (fun x => (l x).zip (l' x)) :=
  Poly.comp Poly.list_zip (Poly.pair hl hl')

@[fun_prop] theorem list_range_length_comp [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => List.range (l x).length) :=
  Poly.comp (f := fun xs : List β => List.range xs.length) Poly.list_indices hl

@[fun_prop] theorem list_any [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).any (f x)) := by
  have h : Poly (fun x => !((as x).filter (f x)).isEmpty) :=
    bool_not_comp (list_isEmpty_comp (Poly.list_filter hf ha))
  refine of_eq h (fun x => ?_)
  induction as x with
  | nil => rfl
  | cons a l ih => cases hfa : f x a <;> simp_all

@[fun_prop] theorem list_all [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).all (f x)) := by
  have h : Poly (fun x => ((as x).filter (fun b => !f x b)).isEmpty) :=
    list_isEmpty_comp (Poly.list_filter (f := fun x b => !f x b) (bool_not_comp hf) ha)
  refine of_eq h (fun x => ?_)
  induction as x with
  | nil => rfl
  | cons a l ih => cases hfa : f x a <;> simp_all

@[fun_prop] theorem pair_contains [Inhabited α] {l : α → List (ℕ × ℕ)} {a : α → ℕ × ℕ}
    (hl : Poly l) (ha : Poly a) : Poly (fun x => (l x).contains (a x)) := by
  have h : Poly (fun x => (l x).any (fun b => b == a x)) := by fun_prop
  refine of_eq h (fun x => ?_)
  induction l x with
  | nil => rfl
  | cons b t ih =>
    rw [List.any_cons, List.contains_cons, ih]
    simp only [beq_eq_decide]
    congr 1
    exact decide_eq_decide.mpr eq_comm

@[fun_prop] theorem nat_bodd : Poly Nat.bodd := ⟨PolyProgram.natOdd⟩

@[fun_prop] theorem mod2_comp {f : α → ℕ} (hf : Poly f) : Poly (fun x => f x % 2 == 1) := by
  have h : Poly (fun x => Nat.bodd (f x)) := Poly.comp nat_bodd hf
  refine of_eq h (fun x => ?_)
  rw [Nat.mod_two_of_bodd]; cases Nat.bodd (f x) <;> rfl

end PA

open PA
set_option linter.unusedSectionVars false

/-! Compositional forms of the assumed field / linear-algebra lemmas -/

section Comp
variable {α : Type} [Coding α]

@[fun_prop] theorem gfZero_c {u : α → List Unit} (hu : Poly u) :
    Poly (fun x => gfZero (u x).length) :=
  Poly.comp (f := fun u : List Unit => gfZero u.length) poly_gfZero hu

@[fun_prop] theorem gfIsZero_c {u : α → List Unit} {a : α → List Bool} (hu : Poly u) (ha : Poly a) :
    Poly (fun x => gfIsZero (u x).length (a x)) :=
  Poly.comp (f := fun p : List Unit × List Bool => gfIsZero p.1.length p.2) poly_gfIsZero
    (Poly.pair hu ha)

@[fun_prop] theorem listSum_c {u : α → List Unit} {a : α → List (List Bool)} (hu : Poly u)
    (ha : Poly a) : Poly (fun x => listSum (gfOps (u x).length) (a x)) :=
  Poly.comp (f := fun p : List Unit × List (List Bool) => listSum (gfOps p.1.length) p.2)
    poly_listSum (Poly.pair hu ha)

@[fun_prop] theorem detAlg_c {u : α → List Unit} {a : α → List (List (List Bool))} (hu : Poly u)
    (ha : Poly a) : Poly (fun x => detAlg (gfOps (u x).length) (a x)) := by
  have := Poly.comp poly_detAlg (Poly.pair hu ha)
  exact this

@[fun_prop] theorem solveF2_c {u : α → List Unit} {a : α → List Eqn} (hu : Poly u)
    (ha : Poly a) : Poly (fun x => solveF2 (u x).length (a x)) := by
  have := Poly.comp poly_solveF2 (Poly.pair hu ha)
  exact this

end Comp

/-! Restated algorithm: the field parameter `m` is a unary list `u`, `List.range N` is a list `R`. -/

def idxPairs' (R : List ℕ) : List (ℕ × ℕ) := R.flatMap (fun i => R.map (fun j => (i, j)))

def validEnc' (w : List Bool) (R : List ℕ) : Bool :=
  decide (hdrN w < w.length) && (encBody w).length == hdrN w * hdrN w &&
    (idxPairs' R).all (fun ij => adjBit w ij.1 ij.2 == adjBit w ij.2 ij.1 &&
      !(ij.1 == ij.2 && adjBit w ij.1 ij.2))

def encEdges' (w : List Bool) (R : List ℕ) : List (ℕ × ℕ) :=
  (idxPairs' R).filter (fun ij => decide (ij.1 < ij.2) && adjBit w ij.1 ij.2)

def weightMatrix' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (β : List (List Bool)) :
    List (List (List Bool)) :=
  R.map (fun i => R.map (fun j =>
    β.getD (E.findIdx (fun e => e == (min i j, max i j))) (gfZero u.length)))

def phiVal' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (β : List (List Bool)) : List Bool :=
  detAlg (gfOps u.length) (weightMatrix' u R E β)

def qVal' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (β : List (List Bool)) : List Bool :=
  listSum (gfOps u.length)
    ([if s then phiVal' u R E β else gfZero u.length] ++
      ((E.zip d).filter (fun ed => ed.2)).map (fun ed => phiVal' u R E (kill u.length E [ed.1] β)) ++
      (crossPairs E).map (fun ef => phiVal' u R E (kill u.length E [ef.1, ef.2] β)))

def vtx' (R : List ℕ) (S : List (ℕ × ℕ)) : ℕ := R.findIdx (fun u => !touches S (u, u))

def cands' (R : List ℕ) (E S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.filter (fun e => (e.1 == vtx' R S || e.2 == vtx' R S) && !touches S e)

def pick' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (α : List (List Bool)) (S : List (ℕ × ℕ)) : ℕ :=
  (cands' R E S).findIdx (fun e => !gfIsZero u.length (qVal' u R E d s (kill u.length E (S ++ [e]) α)))

def searchStep' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (α : List (List Bool)) (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if pick' u R E d s α S < (cands' R E S).length then
    S ++ [(cands' R E S).getD (pick' u R E d s α S) (0, 0)]
  else S

def greedySearch' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (α : List (List Bool)) : List (ℕ × ℕ) :=
  R.foldl (fun S _ => searchStep' u R E d s α S) []

def isPMList' (R : List ℕ) (E S : List (ℕ × ℕ)) : Bool :=
  R.all (fun v => (S.filter (fun f => f.1 == v || f.2 == v)).length == 1) &&
    S.all (fun f => E.contains f)

def solU (E : List (ℕ × ℕ)) (eqs : List Eqn) : Bool × List Bool :=
  solveF2 (E.map (fun _ => ()) ++ [()]).length eqs

def gsR (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (sol : Bool × List Bool)
    (r : ℕ) : List (ℕ × ℕ) :=
  greedySearch' u R E (sol.2.take E.length) (sol.2.getD E.length false) (roundPoint u.length E ρ r)

def roundStep' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool)
    (st : List Eqn × (Bool × Bool)) (r : ℕ) : List Eqn × (Bool × Bool) :=
  if st.2.1 then st
  else if !(solU E st.1).1 then (st.1, (true, false))
  else if gfIsZero u.length (qVal' u R E ((solU E st.1).2.take E.length)
      ((solU E st.1).2.getD E.length false) (roundPoint u.length E ρ r)) then
    (st.1, (true, true))
  else if isPMList' R E (gsR u R E ρ (solU E st.1) r) &&
      violates E ((solU E st.1).2.take E.length) ((solU E st.1).2.getD E.length false)
        (gsR u R E ρ (solU E st.1) r) then
    (st.1 ++ [matchEqn E (gsR u R E ρ (solU E st.1) r)], (false, false))
  else (st.1, (true, true))

def roundsList (E : List (ℕ × ℕ)) : List ℕ := List.range (E ++ [(0, 0), (0, 0), (0, 0)]).length

def runFold (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) :
    List Eqn × (Bool × Bool) :=
  (roundsList E).foldl (roundStep' u R E ρ) ([], (false, false))

def runRounds' (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) : Bool :=
  !(runFold u R E ρ).2.1 || (runFold u R E ρ).2.2

def tripleFold (bs : List Bool) : List Unit := bs.foldl (fun u _ => u ++ u ++ u) [()]

def mU (w : List Bool) : List Unit := tripleFold (hdrN w).bits

def rangeN (w : List Bool) : List ℕ := (List.range w.length).take (hdrN w)

/-! Equalities with the original definitions -/

theorem rangeN_eq (w : List Bool) : rangeN w = List.range (hdrN w) := by
  have h : hdrN w ≤ w.length := List.findIdx_le_length
  simp [rangeN, List.take_range, Nat.min_eq_left h]

theorem tripleFold_length (bs : List Bool) (u : List Unit) :
    (bs.foldl (fun u _ => u ++ u ++ u) u).length = u.length * 3 ^ bs.length := by
  induction bs generalizing u with
  | nil => simp
  | cons b bs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons, pow_succ]; ring

theorem mU_length (w : List Bool) : (mU w).length = fieldM (hdrN w) := by
  unfold mU tripleFold
  rw [tripleFold_length, Nat.size_eq_bits_len]
  simp [fieldM]

theorem validEnc_eq (w : List Bool) : validEnc w = validEnc' w (List.range (hdrN w)) := rfl

theorem encEdges_eq (w : List Bool) : encEdges w = encEdges' w (List.range (hdrN w)) := rfl

theorem roundStep_eq (u : List Unit) (N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) :
    roundStep u.length N E ρ = roundStep' u (List.range N) E ρ := by
  funext st r
  have h : (E.map (fun _ => ()) ++ [()]).length = E.length + 1 := by simp
  unfold roundStep roundStep' gsR
  simp only [solU, h]
  rfl

theorem runRounds_eq (u : List Unit) (N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) :
    runRounds u.length N E ρ = runRounds' u (List.range N) E ρ := by
  have h : roundsList E = List.range (E.length + 3) := by simp [roundsList]
  unfold runRounds runRounds' runFold
  rw [h, roundStep_eq]

theorem pfAlg_eq (x : List Bool × List Bool) :
    pfAlg x = (validEnc' x.2 (rangeN x.2) &&
      runRounds' (mU x.2) (rangeN x.2) (encEdges' x.2 (rangeN x.2)) x.1) := by
  rw [rangeN_eq, pfAlg, validEnc_eq, encEdges_eq, ← mU_length, runRounds_eq]

/-! Poly of the pieces (compositional forms) -/

section Pieces
variable {α : Type} [Coding α] [Inhabited α]

@[fun_prop] theorem hdrN_c {w : α → List Bool} (hw : Poly w) : Poly (fun x => hdrN (w x)) := by
  unfold hdrN; fun_prop

@[fun_prop] theorem encBody_c {w : α → List Bool} (hw : Poly w) : Poly (fun x => encBody (w x)) := by
  unfold encBody; fun_prop

@[fun_prop] theorem adjBit_c {w : α → List Bool} {i j : α → ℕ} (hw : Poly w) (hi : Poly i)
    (hj : Poly j) : Poly (fun x => adjBit (w x) (i x) (j x)) := by
  unfold adjBit; fun_prop

@[fun_prop] theorem idxPairs'_c {R : α → List ℕ} (hR : Poly R) : Poly (fun x => idxPairs' (R x)) := by
  unfold idxPairs'; fun_prop

@[fun_prop] theorem validEnc'_c {w : α → List Bool} {R : α → List ℕ} (hw : Poly w) (hR : Poly R) :
    Poly (fun x => validEnc' (w x) (R x)) := by
  unfold validEnc'; fun_prop

@[fun_prop] theorem encEdges'_c {w : α → List Bool} {R : α → List ℕ} (hw : Poly w) (hR : Poly R) :
    Poly (fun x => encEdges' (w x) (R x)) := by
  unfold encEdges'; fun_prop

@[fun_prop] theorem touches_c {S : α → List (ℕ × ℕ)} {e : α → ℕ × ℕ} (hS : Poly S) (he : Poly e) :
    Poly (fun x => touches (S x) (e x)) := by
  unfold touches; fun_prop

@[fun_prop] theorem kill_c {u : α → List Unit} {E S : α → List (ℕ × ℕ)} {β : α → List (List Bool)}
    (hu : Poly u) (hE : Poly E) (hS : Poly S) (hβ : Poly β) :
    Poly (fun x => kill (u x).length (E x) (S x) (β x)) := by
  unfold kill; fun_prop

@[fun_prop] theorem crossPairs_c {E : α → List (ℕ × ℕ)} (hE : Poly E) :
    Poly (fun x => crossPairs (E x)) := by
  unfold crossPairs; fun_prop

@[fun_prop] theorem weightMatrix'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {β : α → List (List Bool)} (hu : Poly u) (hR : Poly R) (hE : Poly E) (hβ : Poly β) :
    Poly (fun x => weightMatrix' (u x) (R x) (E x) (β x)) := by
  unfold weightMatrix'; fun_prop

@[fun_prop] theorem phiVal'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {β : α → List (List Bool)} (hu : Poly u) (hR : Poly R) (hE : Poly E) (hβ : Poly β) :
    Poly (fun x => phiVal' (u x) (R x) (E x) (β x)) := by
  unfold phiVal'; fun_prop

@[fun_prop] theorem qVal'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {d : α → List Bool} {s : α → Bool}
    {β : α → List (List Bool)} (hu : Poly u) (hR : Poly R) (hE : Poly E) (hd : Poly d) (hs : Poly s)
    (hβ : Poly β) :
    Poly (fun x => qVal' (u x) (R x) (E x) (d x) (s x) (β x)) := by
  unfold qVal'; fun_prop

@[fun_prop] theorem vtx'_c {R : α → List ℕ} {S : α → List (ℕ × ℕ)} (hR : Poly R) (hS : Poly S) :
    Poly (fun x => vtx' (R x) (S x)) := by
  unfold vtx'; fun_prop

@[fun_prop] theorem cands'_c {R : α → List ℕ} {E S : α → List (ℕ × ℕ)} (hR : Poly R) (hE : Poly E)
    (hS : Poly S) : Poly (fun x => cands' (R x) (E x) (S x)) := by
  unfold cands'; fun_prop

@[fun_prop] theorem pick'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {d : α → List Bool} {s : α → Bool} {β : α → List (List Bool)} {S : α → List (ℕ × ℕ)}
    (hu : Poly u) (hR : Poly R) (hE : Poly E) (hd : Poly d) (hs : Poly s) (hβ : Poly β)
    (hS : Poly S) :
    Poly (fun x => pick' (u x) (R x) (E x) (d x) (s x) (β x) (S x)) := by
  unfold pick'; fun_prop

@[fun_prop] theorem searchStep'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {d : α → List Bool} {s : α → Bool} {β : α → List (List Bool)} {S : α → List (ℕ × ℕ)}
    (hu : Poly u) (hR : Poly R) (hE : Poly E) (hd : Poly d) (hs : Poly s) (hβ : Poly β)
    (hS : Poly S) :
    Poly (fun x => searchStep' (u x) (R x) (E x) (d x) (s x) (β x) (S x)) := by
  unfold searchStep'
  exact Poly.ite_prop (by fun_prop) (by fun_prop) hS

@[fun_prop] theorem isPMList'_c {R : α → List ℕ} {E S : α → List (ℕ × ℕ)} (hR : Poly R)
    (hE : Poly E) (hS : Poly S) : Poly (fun x => isPMList' (R x) (E x) (S x)) := by
  unfold isPMList'; fun_prop

@[fun_prop] theorem violates_c {E : α → List (ℕ × ℕ)} {d : α → List Bool} {s : α → Bool}
    {S : α → List (ℕ × ℕ)} (hE : Poly E) (hd : Poly d) (hs : Poly s) (hS : Poly S) :
    Poly (fun x => violates (E x) (d x) (s x) (S x)) := by
  unfold violates crossCount dCount; fun_prop

@[fun_prop] theorem matchEqn_c {E S : α → List (ℕ × ℕ)} (hE : Poly E) (hS : Poly S) :
    Poly (fun x => matchEqn (E x) (S x)) := by
  unfold matchEqn crossCount; fun_prop

@[fun_prop] theorem roundPoint_c {u : α → List Unit} {E : α → List (ℕ × ℕ)} {ρ : α → List Bool}
    {r : α → ℕ} (hu : Poly u) (hE : Poly E) (hρ : Poly ρ) (hr : Poly r) :
    Poly (fun x => roundPoint (u x).length (E x) (ρ x) (r x)) := by
  unfold roundPoint; fun_prop

@[fun_prop] theorem solU_c {E : α → List (ℕ × ℕ)} {eqs : α → List Eqn} (hE : Poly E)
    (he : Poly eqs) : Poly (fun x => solU (E x) (eqs x)) := by
  unfold solU; fun_prop

@[fun_prop] theorem roundsList_c {E : α → List (ℕ × ℕ)} (hE : Poly E) :
    Poly (fun x => roundsList (E x)) := by
  unfold roundsList; fun_prop

@[fun_prop] theorem rangeN_c {w : α → List Bool} (hw : Poly w) : Poly (fun x => rangeN (w x)) := by
  unfold rangeN; fun_prop

end Pieces

/-! Encoding-length facts -/

section EncLen
variable {β γ : Type} [Coding β] [Coding γ]

theorem enc_pair_len (x : β × γ) :
    (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
  encodePair_length enc enc x

theorem enc_fst_le (x : β × γ) : (enc x.1).length ≤ (enc x).length := by
  rw [enc_pair_len]; omega

theorem enc_snd_le (x : β × γ) : (enc x.2).length ≤ (enc x).length := by
  rw [enc_pair_len]; omega

theorem enc_cons_len (a : β) (l : List β) :
    (enc (a :: l)).length = 2 * (enc a).length + 1 + (enc l).length :=
  EncodedList.cons_length enc a l

theorem enc_list_le (l : List β) (K : ℕ) (h : ∀ a ∈ l, (enc a).length ≤ K) :
    (enc l).length ≤ l.length * (2 * K + 1) := by
  induction l with
  | nil => simp [enc, Coding.encode, encodeList]
  | cons a l ih =>
    rw [enc_cons_len]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons]
    nlinarith

theorem enc_mem_le {a : β} {l : List β} (h : a ∈ l) : (enc a).length ≤ (enc l).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [enc_cons_len]
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := ih h'; omega

theorem length_le_enc (l : List β) : l.length ≤ (enc l).length := EncodedList.length_le enc l

theorem enc_unit_list (l : List Unit) : (enc l).length = l.length := by
  induction l with
  | nil => simp [enc, Coding.encode, encodeList]
  | cons a l ih =>
    rw [enc_cons_len, ih]
    have : (enc a).length = 0 := rfl
    simp only [this, List.length_cons]; omega

theorem enc_boollist (l : List Bool) : (enc l).length = 3 * l.length := BooleanLists.length l

end EncLen

theorem foldl_inv {β γ : Type} (P : ℕ → β → Prop) (f : β → γ → β)
    (h : ∀ k b c, P k b → P (k + 1) (f b c)) (L : List γ) :
    ∀ (b : β) (k : ℕ), P k b → P (k + L.length) (L.foldl f b) := by
  induction L with
  | nil => intro b k hb; simpa using hb
  | cons c L ih =>
    intro b k hb
    have := ih (f b c) (k + 1) (h k b c hb)
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm 1] using this

/-! The greedy search fold -/

abbrev GC := List Unit × List ℕ × List (ℕ × ℕ) × List Bool × Bool × List (List Bool)

theorem searchStep'_inv (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool)
    (α : List (List Bool)) (k : ℕ) (S : List (ℕ × ℕ))
    (hS : (∀ e ∈ S, e ∈ E) ∧ S.length ≤ k) :
    (∀ e ∈ searchStep' u R E d s α S, e ∈ E) ∧ (searchStep' u R E d s α S).length ≤ k + 1 := by
  unfold searchStep'
  split_ifs with h
  · refine ⟨?_, by simp; omega⟩
    intro e he
    rcases List.mem_append.1 he with h1 | h1
    · exact hS.1 e h1
    · have he' : e = (cands' R E S).getD (pick' u R E d s α S) (0, 0) := List.mem_singleton.1 h1
      have hm : (cands' R E S).getD (pick' u R E d s α S) (0, 0) ∈ cands' R E S := by
        rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
      rw [he'] at *
      exact (List.mem_filter.1 hm).1
  · exact ⟨hS.1, by omega⟩

theorem greedy_poly0 :
    Poly (fun c : GC => greedySearch' c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2) := by
  unfold greedySearch'
  refine poly_foldl_ctx
    (f := fun (c : GC) (S : List (ℕ × ℕ)) (_ : ℕ) =>
      searchStep' c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 S)
    (init := fun _ => []) (as := fun c => c.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
    (Polynomial.X * (2 * Polynomial.X + 1)) ?_
  intro c n hn
  obtain ⟨h1, h2⟩ := foldl_inv
    (fun k (S : List (ℕ × ℕ)) => (∀ e ∈ S, e ∈ c.2.2.1) ∧ S.length ≤ k)
    (fun S (_ : ℕ) => searchStep' c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 S)
    (fun k S _ hS => searchStep'_inv _ _ _ _ _ _ k S hS) (c.2.1.take n) [] 0 (by simp)
  set L := (enc c).length
  have hE : (enc c.2.2.1).length ≤ L :=
    (enc_fst_le c.2.2).trans ((enc_snd_le c.2).trans (enc_snd_le c))
  have hR : c.2.1.length ≤ L :=
    (length_le_enc _).trans ((enc_fst_le c.2).trans (enc_snd_le c))
  set S := (c.2.1.take n).foldl
    (fun S (_ : ℕ) => searchStep' c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 S) []
  have hK : ∀ e ∈ S, (enc e).length ≤ L := fun e he => (enc_mem_le (h1 e he)).trans hE
  have h3 := enc_list_le S L hK
  have h4 : S.length ≤ L := by
    have : (c.2.1.take n).length ≤ c.2.1.length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    omega
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  calc (enc S).length ≤ S.length * (2 * L + 1) := h3
    _ ≤ L * (2 * L + 1) := Nat.mul_le_mul_right _ h4

attribute [local irreducible] solveF2

section Folds
variable {α : Type} [Coding α] [Inhabited α]

@[fun_prop] theorem greedySearch'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {d : α → List Bool} {s : α → Bool} {β : α → List (List Bool)}
    (hu : Poly u) (hR : Poly R) (hE : Poly E) (hd : Poly d) (hs : Poly s) (hβ : Poly β) :
    Poly (fun x => greedySearch' (u x) (R x) (E x) (d x) (s x) (β x)) := by
  have := Poly.comp greedy_poly0
    (Poly.pair hu (Poly.pair hR (Poly.pair hE (Poly.pair hd (Poly.pair hs hβ)))))
  exact this

@[fun_prop] theorem gsR_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {ρ : α → List Bool} {sol : α → Bool × List Bool} {r : α → ℕ}
    (hu : Poly u) (hR : Poly R) (hE : Poly E) (hρ : Poly ρ) (hsol : Poly sol) (hr : Poly r) :
    Poly (fun x => gsR (u x) (R x) (E x) (ρ x) (sol x) (r x)) := by
  unfold gsR; fun_prop

@[fun_prop] theorem roundStep'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {ρ : α → List Bool} {st : α → List Eqn × (Bool × Bool)} {r : α → ℕ}
    (hu : Poly u) (hR : Poly R) (hE : Poly E) (hρ : Poly ρ) (hst : Poly st) (hr : Poly r) :
    Poly (fun x => roundStep' (u x) (R x) (E x) (ρ x) (st x) (r x)) := by
  unfold roundStep'
  refine Poly.ite (by fun_prop) hst (Poly.ite (by fun_prop) (by fun_prop)
    (Poly.ite (by fun_prop) (by fun_prop) (Poly.ite (by fun_prop) (by fun_prop) (by fun_prop))))

end Folds

/-! The rounds fold -/

abbrev RC := List Unit × List ℕ × List (ℕ × ℕ) × List Bool

theorem roundStep'_fst (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool)
    (st : List Eqn × (Bool × Bool)) (r : ℕ) :
    (roundStep' u R E ρ st r).1 = st.1 ∨
      ∃ S, (roundStep' u R E ρ st r).1 = st.1 ++ [matchEqn E S] := by
  unfold roundStep'
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩

theorem roundStep'_inv (u : List Unit) (R : List ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (k : ℕ)
    (st : List Eqn × (Bool × Bool)) (r : ℕ)
    (hst : (∀ e ∈ st.1, e.1.length = E.length + 1) ∧ st.1.length ≤ k) :
    (∀ e ∈ (roundStep' u R E ρ st r).1, e.1.length = E.length + 1) ∧
      (roundStep' u R E ρ st r).1.length ≤ k + 1 := by
  rcases roundStep'_fst u R E ρ st r with h | ⟨S, h⟩
  · rw [h]; exact ⟨hst.1, by omega⟩
  · rw [h]
    refine ⟨?_, by simp; omega⟩
    intro e he
    rcases List.mem_append.1 he with h1 | h1
    · exact hst.1 e h1
    · rw [List.mem_singleton.1 h1]; simp [matchEqn]

theorem runFold_poly0 : Poly (fun c : RC => runFold c.1 c.2.1 c.2.2.1 c.2.2.2) := by
  unfold runFold
  refine poly_foldl_ctx
    (f := fun (c : RC) (st : List Eqn × (Bool × Bool)) (r : ℕ) =>
      roundStep' c.1 c.2.1 c.2.2.1 c.2.2.2 st r)
    (init := fun _ => ([], (false, false))) (as := fun c => roundsList c.2.2.1)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (2 * (Polynomial.X + 3) * (12 * Polynomial.X + 17) + 5) ?_
  intro c n hn
  obtain ⟨h1, h2⟩ := foldl_inv
    (fun k (st : List Eqn × (Bool × Bool)) =>
      (∀ e ∈ st.1, e.1.length = c.2.2.1.length + 1) ∧ st.1.length ≤ k)
    (fun st r => roundStep' c.1 c.2.1 c.2.2.1 c.2.2.2 st r)
    (fun k st r hst => roundStep'_inv _ _ _ _ k st r hst) ((roundsList c.2.2.1).take n)
    ([], (false, false)) 0 (by simp)
  set L := (enc c).length
  have hE : c.2.2.1.length ≤ L :=
    (length_le_enc _).trans ((enc_fst_le c.2.2).trans ((enc_snd_le c.2).trans (enc_snd_le c)))
  set st := ((roundsList c.2.2.1).take n).foldl
    (fun st r => roundStep' c.1 c.2.1 c.2.2.1 c.2.2.2 st r) ([], (false, false))
  have hK : ∀ e ∈ st.1, (enc e).length ≤ 6 * c.2.2.1.length + 8 := by
    intro e he
    rw [enc_pair_len, enc_boollist, h1 e he]
    have : (enc e.2).length = 1 := rfl
    omega
  have h3 := enc_list_le st.1 _ hK
  have h4 : st.1.length ≤ c.2.2.1.length + 3 := by
    have : ((roundsList c.2.2.1).take n).length ≤ (roundsList c.2.2.1).length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    have hr : (roundsList c.2.2.1).length = c.2.2.1.length + 3 := by simp [roundsList]
    omega
  have h5 : (enc st).length = 2 * (enc st.1).length + 1 + 4 := by
    rw [enc_pair_len]; rfl
  rw [h5]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  have h6 : (enc st.1).length ≤ (L + 3) * (2 * (6 * L + 8) + 1) :=
    h3.trans (Nat.mul_le_mul (by omega) (by omega))
  nlinarith

/-! The unary field parameter -/

theorem nat_bits_poly : Poly (fun n : ℕ => n.bits) :=
  ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem nat_bits_c {α : Type} [Coding α] {n : α → ℕ} (hn : Poly n) :
    Poly (fun x => (n x).bits) := Poly.comp (f := fun n : ℕ => n.bits) nat_bits_poly hn

theorem pow3_size (N : ℕ) : 3 ^ Nat.size N ≤ 3 * N ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hs : 0 < Nat.size N := Nat.size_pos.2 hN
  have h2 : 2 ^ (Nat.size N - 1) ≤ N := by
    by_contra h
    have := Nat.size_le.2 (Nat.lt_of_not_le h)
    omega
  calc 3 ^ Nat.size N = 3 * 3 ^ (Nat.size N - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 3 * 4 ^ (Nat.size N - 1) := by
        gcongr; norm_num
    _ = 3 * (2 ^ (Nat.size N - 1)) ^ 2 := by
        rw [← pow_mul, mul_comm (Nat.size N - 1) 2, pow_mul]; norm_num
    _ ≤ 3 * N ^ 2 := by gcongr
    _ ≤ 3 * N ^ 2 + 1 := by omega

theorem mU_poly : Poly mU := by
  unfold mU tripleFold
  refine poly_foldl_ctx
    (f := fun (_ : List Bool) (u : List Unit) (_ : Bool) => u ++ u ++ u)
    (init := fun _ => [()]) (as := fun w => (hdrN w).bits)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (3 * Polynomial.X ^ 2 + 1) ?_
  intro w n hn
  rw [enc_unit_list, tripleFold_length, enc_boollist]
  simp only [List.length_cons, List.length_nil, zero_add, one_mul, List.length_take,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  have hN : hdrN w ≤ w.length := List.findIdx_le_length
  rw [Nat.size_eq_bits_len] at hn ⊢
  have h1 : 3 ^ min n (hdrN w).size ≤ 3 ^ (hdrN w).size :=
    Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
  have h2 := pow3_size (hdrN w)
  have h3 : hdrN w ^ 2 ≤ (3 * w.length) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-! Assembly -/

section Final
variable {α : Type} [Coding α] [Inhabited α]

@[fun_prop] theorem mU_c {w : α → List Bool} (hw : Poly w) : Poly (fun x => mU (w x)) :=
  Poly.comp mU_poly hw

@[fun_prop] theorem runRounds'_c {u : α → List Unit} {R : α → List ℕ} {E : α → List (ℕ × ℕ)}
    {ρ : α → List Bool} (hu : Poly u) (hR : Poly R) (hE : Poly E) (hρ : Poly ρ) :
    Poly (fun x => runRounds' (u x) (R x) (E x) (ρ x)) := by
  have h : Poly (fun x => runFold (u x) (R x) (E x) (ρ x)) := by
    have := Poly.comp runFold_poly0 (Poly.pair hu (Poly.pair hR (Poly.pair hE hρ)))
    exact this
  unfold runRounds'; fun_prop

end Final

theorem pfAlg_poly : Poly pfAlg := by
  have h : Poly (fun x : List Bool × List Bool => validEnc' x.2 (rangeN x.2) &&
      runRounds' (mU x.2) (rangeN x.2) (encEdges' x.2 (rangeN x.2)) x.1) := by fun_prop
  exact of_eq h (fun x => (pfAlg_eq x).symm)

/-- The whole algorithm, with raw bit strings as inputs. -/
theorem polyProgram_pfAlg : Nonempty (PolyProgram (encodePair id id) encodeBool pfAlg) :=
  ⟨((BooleanLists.packProgram.product BooleanLists.packProgram).comp pfAlg_poly.program).congr _
    (fun _ => rfl)⟩


end PfaffianRecognition.CoRP


open OAI.MetricKMedian.Binary in
theorem solution : Nonempty (PolyProgram (encodePair id id) encodeBool PfaffianRecognition.CoRP.pfAlg) :=
  PfaffianRecognition.CoRP.polyProgram_pfAlg
