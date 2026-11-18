-- Prove2me | solution 1 for SemAC02.lemma_8_10_shifted_distinguisher
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T19:51:22.689444+00:00
-- url     : https://prove2.me/submissions/54ef371c-eea8-45f7-a0ea-5cac4cffc774

import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb
import Definitions.Def_SemAC02_IsCoinDistinguisher
import Mathlib
import Theorems.Thm_SemAC02_theorem_8_9_coin_formulas

section
-- Inlined Solutions.MonotoneCircuitDual

set_option maxHeartbeats 1000000

namespace SemAC02.MonotoneCircuitDual

def dual {V : Type} : Circ V → Circ V
  | .const b => .const (!b)
  | .lit v b => .lit v b
  | .and cs => .or (cs.map dual)
  | .or cs => .and (cs.map dual)
  | .xor cs => .xor (cs.map dual)

theorem dual_dual {V : Type} (C : Circ V) : dual (dual C) = C := by
  cases C with
  | const b => simp [dual]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
  | or cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
  | xor cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem dual_injective {V : Type} : Function.Injective (@dual V) :=
  Function.LeftInverse.injective dual_dual

@[simp] theorem isAnd_dual {V : Type} (C : Circ V) : (dual C).isAnd = C.isOr := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]
@[simp] theorem isOr_dual {V : Type} (C : Circ V) : (dual C).isOr = C.isAnd := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]
@[simp] theorem isXor_dual {V : Type} (C : Circ V) : (dual C).isXor = C.isXor := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]

theorem monotone_dual {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) : IsMonotoneCirc (dual C) := by
  induction hC with
  | const b => simpa only [dual] using IsMonotoneCirc.const (V := V) (!b)
  | lit v => simpa only [dual] using IsMonotoneCirc.lit v
  | and cs hcs ih =>
    rw [dual]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'
  | or cs hcs ih =>
    rw [dual]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'

theorem reduced_dual {V : Type} {C : Circ V} (hC : IsReduced C) : IsReduced (dual C) := by
  induction hC with
  | const b => simpa only [dual] using IsReduced.const (V := V) (!b)
  | lit v b => simpa only [dual] using IsReduced.lit v b
  | and cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.or
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isOr_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | or cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.and
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isAnd_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | xor cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.xor
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isXor_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

theorem depth_dual {V : Type} (C : Circ V) : (dual C).depth = C.depth := by
  cases C with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
  | or cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
  | xor cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem size_dual {V : Type} (C : Circ V) : (dual C).treeSize = C.treeSize := by
  cases C with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
  | or cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
  | xor cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem any_not (bs : List Bool) : (bs.map Bool.not).any id = !(bs.all id) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

theorem all_not (bs : List Bool) : (bs.map Bool.not).all id = !(bs.any id) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

theorem eval_dual {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) (x : V → Bool) :
    (dual C).eval x = !(C.eval (fun i => !x i)) := by
  induction hC with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v => simp [dual,Circ.eval]
  | and cs hcs ih =>
    have he : cs.map (fun c => (dual c).eval x) =
        (cs.map (fun c => c.eval (fun i => !x i))).map Bool.not := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [dual,Circ.eval,List.map_map,Function.comp_def]
    rw [he]
    exact any_not _
  | or cs hcs ih =>
    have he : cs.map (fun c => (dual c).eval x) =
        (cs.map (fun c => c.eval (fun i => !x i))).map Bool.not := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [dual,Circ.eval,List.map_map,Function.comp_def]
    rw [he]
    exact all_not _

end SemAC02.MonotoneCircuitDual
end

section
-- Inlined Solutions.BernoulliAlgebra

open Finset

namespace SemAC02.BernoulliAlgebra

noncomputable def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

noncomputable def weight {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) : ℝ :=
  ∏ i, bitWeight p (x i)

theorem bitWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) : 0 ≤ bitWeight p b := by
  cases b
  · simpa [bitWeight] using sub_nonneg.mpr hp'
  · simpa [bitWeight] using hp

theorem weight_nonneg {I : Type*} [Fintype I] {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (x : I → Bool) :
    0 ≤ weight p x := prod_nonneg (fun _ _ => bitWeight_nonneg hp hp' _)

@[simp] theorem bitWeight_sum (p : ℝ) : ∑ b : Bool, bitWeight p b = 1 := by
  simp [bitWeight]

@[simp] theorem weight_sum (I : Type*) [Fintype I] [DecidableEq I] (p : ℝ) : ∑ x : I → Bool, weight p x = 1 := by
  simp only [weight]
  rw [← Fintype.prod_sum]
  simp only [bitWeight_sum,prod_const_one]

theorem bernProb_eq_weight (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E = ∑ x, if E x then weight p x else 0 := rfl

@[simp] theorem prob_true (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => true) = 1 := by
  simp [bernProb_eq_weight]

@[simp] theorem prob_false (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => false) = 0 := by
  simp [bernProb_eq_weight]

theorem prob_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    0 ≤ bernProb p E := by
  rw [bernProb_eq_weight]
  apply sum_nonneg
  intro x _
  split_ifs
  · exact weight_nonneg hp hp' x
  · exact le_rfl

theorem prob_le_one {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E ≤ 1 := by
  rw [bernProb_eq_weight,← weight_sum (Fin m) p]
  apply sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact weight_nonneg hp hp' x

theorem prob_add_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E + bernProb p (fun x => !E x) = 1 := by
  rw [bernProb_eq_weight,bernProb_eq_weight,← sum_add_distrib,← weight_sum (Fin m) p]
  apply sum_congr rfl
  intro x _
  cases he : E x <;> simp [he]

theorem prob_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => !E x) = 1-bernProb p E := by
  linarith [prob_add_compl p E]

def complementEquiv (I : Type*) : (I → Bool) ≃ (I → Bool) where
  toFun x i := !x i
  invFun x i := !x i
  left_inv x := by funext i; simp only [Bool.not_not]
  right_inv x := by funext i; simp only [Bool.not_not]

theorem bitWeight_compl (p : ℝ) (b : Bool) : bitWeight p (!b) = bitWeight (1-p) b := by
  cases b <;> simp [bitWeight]

theorem weight_compl {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) :
    weight p (complementEquiv I x) = weight (1-p) x := by
  unfold weight
  apply prod_congr rfl
  intro i _
  exact bitWeight_compl p (x i)

theorem prob_complement_inputs (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => E (fun i => !x i)) = bernProb (1-p) E := by
  rw [bernProb_eq_weight,bernProb_eq_weight]
  have he := Equiv.sum_comp (complementEquiv (Fin m))
    (fun x => if E (fun i => !x i) then weight p x else 0)
  rw [← he]
  apply sum_congr rfl
  intro x _
  simp only [complementEquiv,Equiv.coe_fn_mk,Bool.not_not]
  exact congrArg (fun w : ℝ => if E x then w else 0) (weight_compl p x)

end SemAC02.BernoulliAlgebra
end

section
-- Inlined Solutions.CoinFormulaRooting

set_option maxHeartbeats 1000000

open SemAC02.MonotoneCircuitDual SemAC02.BernoulliAlgebra

namespace SemAC02.CoinFormulaRooting

theorem dual_coin {m : ℕ} {C : Circ (Fin m)} (hC : IsMonotoneCirc C) (ε η : ℝ)
    (hc : IsCoinDistinguisher ε η (fun x => C.eval x)) :
    IsCoinDistinguisher ε η (fun x => (dual C).eval x) := by
  rcases hc with ⟨hl,hh⟩
  constructor
  · calc
      _ = bernProb ((1-ε)/2) (fun x => !C.eval (fun i => !x i)) := by
        congr 1
        funext x
        exact eval_dual hC x
      _ = bernProb (1-(1-ε)/2) (fun x => !C.eval x) :=
        prob_complement_inputs ((1-ε)/2) (fun x => !C.eval x)
      _ = bernProb ((1+ε)/2) (fun x => !C.eval x) := by congr 1; ring
      _ ≤ η := hh
  · calc
      _ = bernProb ((1+ε)/2) (fun x => C.eval (fun i => !x i)) := by
        congr 1
        funext x
        simp only [eval_dual hC,Bool.not_not]
      _ = bernProb (1-(1+ε)/2) (fun x => C.eval x) :=
        prob_complement_inputs ((1+ε)/2) (fun x => C.eval x)
      _ = bernProb ((1-ε)/2) (fun x => C.eval x) := by congr 1; ring
      _ ≤ η := hl

def wrapAnd {V : Type} (C : Circ V) : Circ V := .and [C]

@[simp] theorem eval_wrap {V : Type} (C : Circ V) (x : V → Bool) : (wrapAnd C).eval x = C.eval x := by
  simp [wrapAnd,Circ.eval]

theorem monotone_wrap {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) : IsMonotoneCirc (wrapAnd C) := by
  apply IsMonotoneCirc.and
  intro c hc
  simpa only [List.mem_singleton.mp hc] using hC

theorem reduced_wrap {V : Type} {C : Circ V} (hC : IsReduced C) (ht : C.isAnd = false) : IsReduced (wrapAnd C) := by
  apply IsReduced.and
  · simp
  · intro c hc
    simpa only [List.mem_singleton.mp hc] using ht
  · intro c hc
    simpa only [List.mem_singleton.mp hc] using hC

theorem depth_wrap {V : Type} (C : Circ V) : (wrapAnd C).depth = 1+C.depth := by simp [wrapAnd,Circ.depth]
theorem size_wrap {V : Type} (C : Circ V) : (wrapAnd C).treeSize = C.treeSize+1 := by simp [wrapAnd,Circ.treeSize,Nat.add_comm]

theorem and_rooted_variant {m : ℕ} (C : Circ (Fin m)) (hC : IsMonotoneCirc C) (hR : IsReduced C)
    (ε η : ℝ) (hc : IsCoinDistinguisher ε η (fun x => C.eval x)) :
    ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧ (∃ cs, T = Circ.and cs) ∧
      T.depth ≤ max C.depth 1 ∧ T.treeSize ≤ C.treeSize+1 ∧
      IsCoinDistinguisher ε η (fun x => T.eval x) := by
  cases hC with
  | const b =>
    refine ⟨wrapAnd (.const b),monotone_wrap (.const b),reduced_wrap hR rfl,⟨[.const b],rfl⟩,?_,?_,?_⟩
    · simp [depth_wrap,Circ.depth]
    · rw [size_wrap]
    · simpa only [eval_wrap] using hc
  | lit v =>
    refine ⟨wrapAnd (.lit v true),monotone_wrap (.lit v),reduced_wrap hR rfl,⟨[.lit v true],rfl⟩,?_,?_,?_⟩
    · simp [depth_wrap,Circ.depth]
    · rw [size_wrap]
    · simpa only [eval_wrap] using hc
  | and cs hcs =>
    exact ⟨.and cs,.and cs hcs,hR,⟨cs,rfl⟩,le_max_left _ _,by omega,hc⟩
  | or cs hcs =>
    have hM := IsMonotoneCirc.or cs hcs
    refine ⟨dual (.or cs),monotone_dual hM,reduced_dual hR,⟨cs.map dual,?_⟩,?_,?_,dual_coin hM ε η hc⟩
    · rw [dual]
    · rw [depth_dual]; exact le_max_left _ _
    · rw [size_dual]; omega

theorem prob_zero (p : ℝ) (E : (Fin 0 → Bool) → Bool) :
    bernProb p E = if E (fun _ => false) then 1 else 0 := by
  letI : Unique (Fin 0 → Bool) := ⟨⟨fun _ => false⟩,fun _ => funext (fun i => Fin.elim0 i)⟩
  simp only [bernProb,Fintype.sum_unique,Finset.univ_eq_empty,Finset.prod_empty]
  rfl

theorem coin_dimension_pos {m : ℕ} (E : (Fin m → Bool) → Bool) (ε η : ℝ) (hη : η < 1)
    (hc : IsCoinDistinguisher ε η E) : 1 ≤ m := by
  cases m with
  | zero =>
    rcases hc with ⟨hl,hh⟩
    rw [prob_zero] at hl hh
    cases he : E (fun _ => false) <;> simp [he] at hl hh <;> linarith
  | succ m => omega

end SemAC02.CoinFormulaRooting
end

section
-- Inlined Solutions.FiniteProductPushforward

open Finset

namespace ProofComplexity.FiniteProductPushforward

theorem prod_fiber_indicator {I A B : Type*} [Fintype I] [DecidableEq I] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (x : I → A) (y : I → B) :
    (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, if g (x i) = y i then w i (x i) else 0 := by
  classical
  by_cases he : (fun i => g (x i)) = y
  · rw [if_pos he]
    apply prod_congr rfl
    intro i _
    rw [if_pos (congrFun he i)]
  · rw [if_neg he]
    obtain ⟨i,hi⟩ : ∃ i, g (x i) ≠ y i := by
      by_contra! h
      exact he (funext h)
    symm
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem fiber_weight {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (y : I → B) :
    (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ a : A, if g a = y i then w i a else 0 := by
  classical
  simp_rw [prod_fiber_indicator]
  exact (Fintype.prod_sum (fun i : I => fun a : A => if g a = y i then w i a else 0)).symm

/-- Independent finite coordinates remain independent under a coordinatewise map. -/
theorem sum_pushforward {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B] [DecidableEq B]
    (g : A → B) (w : I → A → ℝ) (F : (I → B) → ℝ) :
    (∑ x : I → A, (∏ i, w i (x i))*F (fun i => g (x i))) =
      ∑ y : I → B, (∏ i, ∑ a : A, if g a = y i then w i a else 0)*F y := by
  classical
  calc
    _ = ∑ x : I → A, ∑ y : I → B,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      apply sum_congr rfl
      intro x _
      simp only [ite_mul,zero_mul]
      simp
    _ = ∑ y : I → B, ∑ x : I → A,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := sum_comm
    _ = ∑ y : I → B,
        (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      simp only [sum_mul]
    _ = _ := by simp only [fiber_weight]

end ProofComplexity.FiniteProductPushforward
end

section
-- Inlined Solutions.BernoulliPinning

open Finset
open ProofComplexity.FiniteProductPushforward

namespace SemAC02.BernoulliAlgebra

def pairEquiv (I : Type*) : (I → Bool × Bool) ≃ (I → Bool) × (I → Bool) where
  toFun x := (fun i => (x i).1,fun i => (x i).2)
  invFun x i := (x.1 i,x.2 i)
  left_inv x := by funext i; rfl
  right_inv x := by cases x; rfl

def unionInputs {I : Type*} (x y : I → Bool) : I → Bool := fun i => x i || y i

theorem or_bit_weight (p q : ℝ) (b : Bool) :
    (∑ a : Bool × Bool, if (a.1 || a.2) = b then bitWeight p a.1 * bitWeight q a.2 else 0) =
      bitWeight (p+(1-p)*q) b := by
  cases b <;> simp [Fintype.sum_prod_type,Fintype.sum_bool,bitWeight] <;> ring

theorem prob_eq_indicator (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E = ∑ x, weight p x * (if E x then 1 else 0) := by
  simp only [bernProb_eq_weight,mul_ite,mul_one,mul_zero]

/-- Randomly pinning each coordinate to one changes the product bias to p+(1-p)q. -/
theorem pinning_average (p q : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    (∑ z : Fin m → Bool, weight p z * bernProb q (fun x => E (unionInputs z x))) =
      bernProb (p+(1-p)*q) E := by
  classical
  let F : (Fin m → Bool) → ℝ := fun y => if E y then 1 else 0
  have he := Equiv.sum_comp (pairEquiv (Fin m))
    (fun z : (Fin m → Bool) × (Fin m → Bool) => weight p z.1 * weight q z.2 * F (unionInputs z.1 z.2))
  have hp := sum_pushforward (I := Fin m) (A := Bool × Bool) (B := Bool)
    (fun a => a.1 || a.2) (fun _ a => bitWeight p a.1 * bitWeight q a.2) F
  calc
    _ = ∑ z : (Fin m → Bool) × (Fin m → Bool), weight p z.1 * weight q z.2 * F (unionInputs z.1 z.2) := by
      rw [Fintype.sum_prod_type]
      simp only [prob_eq_indicator,mul_sum,mul_assoc,F]
    _ = ∑ z : Fin m → Bool × Bool,
        weight p (fun i => (z i).1) * weight q (fun i => (z i).2) * F (fun i => (z i).1 || (z i).2) := he.symm
    _ = ∑ y : Fin m → Bool, weight (p+(1-p)*q) y * F y := by
      simpa only [weight,prod_mul_distrib,or_bit_weight] using hp
    _ = _ := (prob_eq_indicator _ E).symm

theorem bitWeight_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) (b : Bool) : 0 < bitWeight p b := by
  cases b
  · simpa [bitWeight] using sub_pos.mpr hp'
  · simpa [bitWeight] using hp

theorem weight_pos {I : Type*} [Fintype I] {p : ℝ} (hp : 0 < p) (hp' : p < 1) (x : I → Bool) :
    0 < weight p x := prod_pos (fun _ _ => bitWeight_pos hp hp' _)

theorem exists_at_most_average {p : ℝ} (hp : 0 < p) (hp' : p < 1) {m : ℕ}
    (f : (Fin m → Bool) → ℝ) (η : ℝ) (hf : (∑ x, weight p x*f x) ≤ η) :
    ∃ x, f x ≤ η := by
  classical
  by_contra! hx
  have hs : (∑ x : Fin m → Bool, weight p x*η) < ∑ x, weight p x*f x := by
    apply sum_lt_sum
    · intro x _
      exact (mul_lt_mul_of_pos_left (hx x) (weight_pos hp hp' x)).le
    · exact ⟨fun _ => false,mem_univ _,mul_lt_mul_of_pos_left (hx _) (weight_pos hp hp' _)⟩
  rw [← sum_mul,weight_sum,one_mul] at hs
  linarith

/-- The probabilistic substitution step of the shifted coin distinguisher, Lemma 8.10. -/
theorem exists_shifted_pinning {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1/2) {m : ℕ}
    (E : (Fin m → Bool) → Bool)
    (hl : bernProb ((1-ε/(1+ε))/2) E ≤ 1/10)
    (hh : bernProb ((1+ε/(1+ε))/2) (fun x => !E x) ≤ 1/10) :
    ∃ z : Fin m → Bool,
      bernProb (1/2-ε) (fun x => E (unionInputs z x)) ≤ 1/5 ∧
      bernProb (1/2) (fun x => !E (unionInputs z x)) ≤ 1/5 := by
  classical
  let δ := ε/(1+ε)
  have hden : 0 < 1+ε := by linarith
  have hδ₀ : 0 < δ := div_pos hε₀ hden
  have hδ : δ < 1 := (div_lt_one hden).mpr (by linarith)
  have hbiasl : δ+(1-δ)*(1/2-ε) = (1-δ)/2 := by
    dsimp only [δ]
    field_simp [ne_of_gt hden]
    <;> ring
  have hbiash : δ+(1-δ)*(1/2) = (1+δ)/2 := by ring
  let f : (Fin m → Bool) → ℝ := fun z =>
    bernProb (1/2-ε) (fun x => E (unionInputs z x)) +
      bernProb (1/2) (fun x => !E (unionInputs z x))
  have havg : (∑ z, weight δ z*f z) ≤ 1/5 := by
    dsimp only [f]
    simp_rw [mul_add]
    rw [sum_add_distrib,pinning_average δ (1/2-ε) E,pinning_average δ (1/2) (fun x => !E x),hbiasl,hbiash]
    linarith
  obtain ⟨z,hz⟩ := exists_at_most_average hδ₀ hδ f (1/5) havg
  have hlow := prob_nonneg (show (0 : ℝ) ≤ 1/2-ε by linarith)
    (show (1/2 : ℝ)-ε ≤ 1 by linarith) (fun x => E (unionInputs z x))
  have hhigh := prob_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ) ≤ 1 by norm_num) (fun x => !E (unionInputs z x))
  exact ⟨z,by dsimp only [f] at hz; constructor <;> linarith⟩

end SemAC02.BernoulliAlgebra
end

section
-- Inlined Solutions.MonotoneCircuitPinning

set_option maxHeartbeats 1000000

namespace SemAC02.MonotoneCircuitPinning

open Classical in
noncomputable def pin {V : Type} (z : V → Bool) : Circ V → Circ V
  | .const b => .const b
  | .lit v b => if z v then .const b else .lit v b
  | .and cs => .and (cs.map (pin z)).dedup
  | .or cs => .or (cs.map (pin z)).dedup
  | .xor cs => .xor (cs.map (pin z))

@[simp] theorem isAnd_pin {V : Type} (z : V → Bool) (C : Circ V) : (pin z C).isAnd = C.isAnd := by
  cases C with
  | const b => simp only [pin,Circ.isAnd]
  | lit v b => rw [pin]; split_ifs <;> rfl
  | and cs => rw [pin]; rfl
  | or cs => rw [pin]; rfl
  | xor cs => rw [pin]; rfl

@[simp] theorem isOr_pin {V : Type} (z : V → Bool) (C : Circ V) : (pin z C).isOr = C.isOr := by
  cases C with
  | const b => simp only [pin,Circ.isOr]
  | lit v b => rw [pin]; split_ifs <;> rfl
  | and cs => rw [pin]; rfl
  | or cs => rw [pin]; rfl
  | xor cs => rw [pin]; rfl

theorem monotone_pin {V : Type} (z : V → Bool) {C : Circ V} (hC : IsMonotoneCirc C) : IsMonotoneCirc (pin z C) := by
  classical
  induction hC with
  | const b => rw [pin]; exact .const _
  | lit v => rw [pin]; split <;> constructor
  | and cs hcs ih =>
    rw [pin]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
    exact ih c' hc'
  | or cs hcs ih =>
    rw [pin]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
    exact ih c' hc'

theorem reduced_pin {V : Type} (z : V → Bool) {C : Circ V}
    (hC : IsMonotoneCirc C) (hR : IsReduced C) : IsReduced (pin z C) := by
  classical
  induction hC with
  | const b => rw [pin]; exact .const _
  | lit v => rw [pin]; split <;> constructor
  | and cs hcs ih =>
    cases hR with
    | and _ _ htype hred =>
      rw [pin]
      apply IsReduced.and
      · exact List.nodup_dedup _
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        simpa only [isAnd_pin] using htype c' hc'
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        exact ih c' hc' (hred c' hc')
  | or cs hcs ih =>
    cases hR with
    | or _ _ htype hred =>
      rw [pin]
      apply IsReduced.or
      · exact List.nodup_dedup _
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        simpa only [isOr_pin] using htype c' hc'
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        exact ih c' hc' (hred c' hc')

theorem all_dedup {α : Type*} [DecidableEq α] (cs : List α) (f : α → Bool) : cs.dedup.all f = cs.all f := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem any_dedup {α : Type*} [DecidableEq α] (cs : List α) (f : α → Bool) : cs.dedup.any f = cs.any f := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem eval_pin {V : Type} (z : V → Bool) {C : Circ V} (hC : IsMonotoneCirc C) (x : V → Bool) :
    (pin z C).eval x = C.eval (BernoulliAlgebra.unionInputs z x) := by
  classical
  induction hC with
  | const b => simp only [pin,Circ.eval]
  | lit v => cases hz : z v <;> simp [pin,Circ.eval,BernoulliAlgebra.unionInputs,hz]
  | and cs hcs ih =>
    have he : cs.map (fun c => (pin z c).eval x) = cs.map (fun c => c.eval (BernoulliAlgebra.unionInputs z x)) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [pin,Circ.eval,List.all_map,all_dedup,Function.comp_def]
    simpa only [List.all_map,Function.comp_def] using congrArg (fun bs : List Bool => bs.all id) he
  | or cs hcs ih =>
    have he : cs.map (fun c => (pin z c).eval x) = cs.map (fun c => c.eval (BernoulliAlgebra.unionInputs z x)) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [pin,Circ.eval,List.any_map,any_dedup,Function.comp_def]
    simpa only [List.any_map,Function.comp_def] using congrArg (fun bs : List Bool => bs.any id) he

theorem dedup_max_le {α : Type*} [DecidableEq α] (cs : List α) (f : α → ℕ) :
    (cs.dedup.map f).foldr max 0 ≤ (cs.map f).foldr max 0 := by
  apply List.max_le_of_forall_le
  intro v hv
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
  exact List.le_max_of_le (List.mem_map.mpr ⟨c,List.mem_dedup.mp hc,rfl⟩) le_rfl

theorem map_max_mono {α : Type*} (cs : List α) (f g : α → ℕ) (hfg : ∀ c ∈ cs, f c ≤ g c) :
    (cs.map f).foldr max 0 ≤ (cs.map g).foldr max 0 := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    simp only [List.map_cons,List.foldr_cons]
    exact max_le_max (hfg c (List.mem_cons_self)) (ih (fun a ha => hfg a (List.mem_cons_of_mem c ha)))

theorem depth_pin {V : Type} (z : V → Bool) (C : Circ V) : (pin z C).depth ≤ C.depth := by
  classical
  cases C with
  | const b => simp only [pin,Circ.depth,le_refl]
  | lit v b => rw [pin]; split <;> simp only [Circ.depth,le_refl]
  | and cs =>
    have hm := map_max_mono cs (fun c => (pin z c).depth) Circ.depth (fun c hc => depth_pin z c)
    have hd := dedup_max_le (cs.map (pin z)) Circ.depth
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [pin,Circ.depth] using Nat.add_le_add_left (hd.trans hm) 1
  | or cs =>
    have hm := map_max_mono cs (fun c => (pin z c).depth) Circ.depth (fun c hc => depth_pin z c)
    have hd := dedup_max_le (cs.map (pin z)) Circ.depth
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [pin,Circ.depth] using Nat.add_le_add_left (hd.trans hm) 1
  | xor cs =>
    have hm := map_max_mono cs (fun c => (pin z c).depth) Circ.depth (fun c hc => depth_pin z c)
    simpa only [pin,Circ.depth,List.map_map,Function.comp_def] using Nat.add_le_add_left hm 1
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem dedup_sum_le {α : Type*} [DecidableEq α] (cs : List α) (f : α → ℕ) :
    (cs.dedup.map f).sum ≤ (cs.map f).sum :=
  (List.Sublist.map f (List.dedup_sublist cs)).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem size_pin {V : Type} (z : V → Bool) (C : Circ V) : (pin z C).treeSize ≤ C.treeSize := by
  classical
  cases C with
  | const b => simp only [pin,Circ.treeSize,le_refl]
  | lit v b => rw [pin]; split <;> simp only [Circ.treeSize,le_refl]
  | and cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (pin z c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_pin z c)
    have hd := dedup_sum_le (cs.map (pin z)) Circ.treeSize
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [pin,Circ.treeSize] using Nat.add_le_add_left (hd.trans hm) 1
  | or cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (pin z c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_pin z c)
    have hd := dedup_sum_le (cs.map (pin z)) Circ.treeSize
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [pin,Circ.treeSize] using Nat.add_le_add_left (hd.trans hm) 1
  | xor cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (pin z c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_pin z c)
    simpa only [pin,Circ.treeSize,List.map_map,Function.comp_def] using Nat.add_le_add_left hm 1
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

end SemAC02.MonotoneCircuitPinning
end

section
-- Inlined Solutions.CoinShiftParameters

set_option maxHeartbeats 1000000

namespace SemAC02.CoinShiftParameters

theorem shift_pos {ε : ℝ} (hε : 0 < ε) : 0 < ε/(1+ε) := div_pos hε (by linarith)

theorem shift_lt {ε : ℝ} (hε : 0 < ε) : ε/(1+ε) < ε := by
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 1+ε)).mpr
  nlinarith [sq_pos_of_pos hε]

theorem shifted_scale_bound {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d) :
    (ε/(1+ε))^(-1/((d : ℝ)-1)) ≤ 2*ε^(-1/((d : ℝ)-1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let e := 1/((d : ℝ)-1)
  have he : e ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < (d : ℝ)-1)).mpr (by linarith)
  have hexp : -1/((d : ℝ)-1) = -e := by dsimp only [e]; ring
  rw [hexp]
  have hden : 0 < 1+ε := by linarith
  have hident : (ε/(1+ε))^(-e) = ε^(-e)*(1+ε)^e := by
    rw [Real.div_rpow hε₀.le hden.le,Real.rpow_neg hden.le,div_inv_eq_mul]
  have hpow : (1+ε)^e ≤ 2 :=
    (Real.rpow_le_self_of_one_le (by linarith) he).trans (by linarith)
  rw [hident]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hε₀.le (-e))

theorem scale_ge_one {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ ε^(-1/((d : ℝ)-1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε₀ hε
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)

/-- Absorb the root-normalisation overhead into the source's uniform exponential constant. -/
theorem size_absorption {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d)
    (A : ℝ) (s : ℕ) (hs : (s : ℝ) ≤ Real.exp (A*(ε/(1+ε))^(-1/((d : ℝ)-1)))) :
    ((s+1 : ℕ) : ℝ) ≤ Real.exp ((2*(abs A)+1)*ε^(-1/((d : ℝ)-1))) := by
  let L := ε^(-1/((d : ℝ)-1))
  let L' := (ε/(1+ε))^(-1/((d : ℝ)-1))
  have hL : 1 ≤ L := scale_ge_one hε₀ hε hd
  have hL' : 0 ≤ L' := Real.rpow_nonneg (shift_pos hε₀).le _
  have hbound : L' ≤ 2*L := shifted_scale_bound hε₀ hε hd
  have hcoeff : A*L' ≤ (2*(abs A))*L := by
    calc
      _ ≤ (abs A)*L' := mul_le_mul_of_nonneg_right (le_abs_self A) hL'
      _ ≤ (abs A)*(2*L) := mul_le_mul_of_nonneg_left hbound (abs_nonneg A)
      _ = _ := by ring
  have hs' : (s : ℝ) ≤ Real.exp ((2*(abs A))*L) := hs.trans (Real.exp_le_exp.mpr hcoeff)
  have hP : 1 ≤ Real.exp ((2*(abs A))*L) := Real.one_le_exp_iff.mpr (by positivity)
  have hE : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ = (s : ℝ)+1 := by simp
    _ ≤ Real.exp ((2*(abs A))*L)+1 := by linarith
    _ ≤ 2*Real.exp ((2*(abs A))*L) := by linarith
    _ ≤ Real.exp ((2*(abs A))*L)*Real.exp L := by
      nlinarith [mul_le_mul_of_nonneg_left hE (Real.exp_nonneg ((2*(abs A))*L))]
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [L]; ring

end SemAC02.CoinShiftParameters
end

section
-- Inlined Solutions.ShiftedCoinDistinguisher

set_option maxHeartbeats 1000000

open SemAC02.CoinFormulaRooting SemAC02.MonotoneCircuitPinning
open SemAC02.CoinShiftParameters SemAC02.BernoulliAlgebra

namespace SemAC02.ShiftedCoinDistinguisher

theorem shifted_distinguisher (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ 1 / 5 ∧
        bernProb (1 / 2) (fun x => !T.eval x) ≤ 1 / 5  := by
  classical
  obtain ⟨A,ε₀,hε₀,hform⟩ := theorem_8_9_coin_formulas d hd
  refine ⟨2*(abs A)+1,min ε₀ (1/2),lt_min hε₀ (by norm_num),?_⟩
  intro ε hεpos hεsmall
  have hsmall := lt_min_iff.mp hεsmall
  have hεhalf : ε < 1/2 := hsmall.2
  have hεone : ε ≤ 1 := by linarith
  let δ := ε/(1+ε)
  have hδpos : 0 < δ := shift_pos hεpos
  have hδε : δ < ε := shift_lt hεpos
  obtain ⟨m,C,hC,hCR,hCd,hCs,hcoin⟩ := hform δ hδpos (hδε.trans hsmall.1)
  have hm : 1 ≤ m := coin_dimension_pos (fun x => C.eval x) δ (1/10) (by norm_num) hcoin
  obtain ⟨T,hT,hTR,⟨cs,hroot⟩,hTd,hTs,hcoinT⟩ := and_rooted_variant C hC hCR δ (1/10) hcoin
  obtain ⟨z,hlo,hhi⟩ := exists_shifted_pinning hεpos hεhalf (fun x => T.eval x) hcoinT.1 hcoinT.2
  refine ⟨m,hm,pin z T,monotone_pin z hT,reduced_pin z hT hTR,?_,?_,?_,?_,?_⟩
  · exact ⟨(cs.map (pin z)).dedup,by rw [hroot,pin]⟩
  · exact (depth_pin z T).trans (hTd.trans (max_le hCd (by omega)))
  · have hp : ((pin z T).treeSize : ℝ) ≤ ((C.treeSize+1 : ℕ) : ℝ) := by
      exact_mod_cast (size_pin z T).trans hTs
    exact hp.trans (size_absorption hεpos hεone hd A C.treeSize hCs)
  · simpa only [eval_pin z hT] using hlo
  · simpa only [eval_pin z hT] using hhi

end SemAC02.ShiftedCoinDistinguisher
end

open SemAC02

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ 1 / 5 ∧
        bernProb (1 / 2) (fun x => !T.eval x) ≤ 1 / 5  := by
  exact SemAC02.ShiftedCoinDistinguisher.shifted_distinguisher d hd
