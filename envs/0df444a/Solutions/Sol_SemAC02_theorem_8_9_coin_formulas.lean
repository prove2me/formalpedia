-- Prove2me | solution 1 for SemAC02.theorem_8_9_coin_formulas
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T20:24:27.937977+00:00
-- url     : https://prove2.me/submissions/f3cbc8a7-af7d-4d48-8ee0-8d7186fbc797

import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb
import Mathlib
import Definitions.Def_SemAC02_IsCoinDistinguisher

section
-- Inlined Solutions.CircuitRenaming

set_option maxHeartbeats 1000000

namespace SemAC02.CircuitRenaming

theorem eval_rename {V W : Type} (f : V → W) (C : Circ V) (x : W → Bool) :
    (C.rename f).eval x = C.eval (x ∘ f) := by
  cases C with
  | const b => simp [Circ.rename,Circ.eval]
  | lit v b => simp [Circ.rename,Circ.eval,Function.comp_def]
  | and cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
  | or cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
  | xor cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_comp {U V W : Type} (f : U → V) (g : V → W) (C : Circ U) :
    (C.rename f).rename g = C.rename (g ∘ f) := by
  cases C with
  | const b => simp [Circ.rename]
  | lit v b => simp [Circ.rename,Function.comp_def]
  | and cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
  | or cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
  | xor cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_id {V : Type} (C : Circ V) : C.rename id = C := by
  cases C with
  | const b => simp [Circ.rename]
  | lit v b => simp [Circ.rename]
  | and cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
  | or cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
  | xor cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_leftInverse {V W : Type} (f : V → W) (g : W → V)
    (hg : Function.LeftInverse g f) : Function.LeftInverse (Circ.rename g) (Circ.rename f) := by
  intro C
  rw [rename_comp,show g ∘ f = id from funext hg,rename_id]

theorem rename_injective {V W : Type} [Nonempty V] (f : V → W) (hf : Function.Injective f) :
    Function.Injective (Circ.rename f) :=
  (rename_leftInverse f (Function.invFun f) (Function.leftInverse_invFun hf)).injective

@[simp] theorem isAnd_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isAnd = C.isAnd := by cases C <;> simp [Circ.rename,Circ.isAnd]
@[simp] theorem isOr_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isOr = C.isOr := by cases C <;> simp [Circ.rename,Circ.isOr]
@[simp] theorem isXor_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isXor = C.isXor := by cases C <;> simp [Circ.rename,Circ.isXor]

theorem monotone_rename {V W : Type} (f : V → W) {C : Circ V} (hC : IsMonotoneCirc C) :
    IsMonotoneCirc (C.rename f) := by
  induction hC with
  | const b => rw [Circ.rename]; constructor
  | lit v => rw [Circ.rename]; constructor
  | and cs hcs ih =>
    rw [Circ.rename]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'
  | or cs hcs ih =>
    rw [Circ.rename]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'

theorem reduced_rename {V W : Type} [Nonempty V] (f : V → W) (hf : Function.Injective f)
    {C : Circ V} (hC : IsReduced C) : IsReduced (C.rename f) := by
  induction hC with
  | const b => rw [Circ.rename]; constructor
  | lit v b => rw [Circ.rename]; constructor
  | and cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.and _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isAnd_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | or cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.or _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isOr_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | xor cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.xor _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isXor_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

theorem depth_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).depth = C.depth := by
  cases C with
  | const b => simp [Circ.rename,Circ.depth]
  | lit v b => simp [Circ.rename,Circ.depth]
  | and cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
  | or cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
  | xor cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem size_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).treeSize = C.treeSize := by
  cases C with
  | const b => simp [Circ.rename,Circ.treeSize]
  | lit v b => simp [Circ.rename,Circ.treeSize]
  | and cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
  | or cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
  | xor cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

end SemAC02.CircuitRenaming
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
-- Inlined Solutions.BernoulliProduct

set_option maxHeartbeats 1000000

open Finset SemAC02.BernoulliAlgebra

namespace SemAC02.BernoulliProduct

/-- The same finite product probability on an arbitrary finite coordinate type. -/
noncomputable def prob {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) : ℝ :=
  ∑ x, if E x then weight p x else 0

theorem prob_complement {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun x => !E x) = 1-prob p E := by
  classical
  have h : prob p E + prob p (fun x => !E x) = 1 := by
    rw [prob,prob,← sum_add_distrib,← weight_sum I p]
    apply sum_congr rfl
    intro x _
    cases he : E x <;> simp [he]
  linarith

theorem prob_all_coordinates {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    prob p (fun x : I → Bool => decide (∀ i, x i = true)) = p ^ Fintype.card I := by
  classical
  unfold prob
  have he : (fun x : I → Bool => if decide (∀ i, x i = true) then weight p x else 0) =
      (fun x => if x = (fun _ => true) then weight p x else 0) := by
    funext x
    congr 1
    simp only [decide_eq_true_eq,funext_iff]
  rw [he]
  simp [weight,bitWeight]

theorem prob_fin {m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p E = bernProb p E := rfl

def assignmentEquiv {I J : Type*} (e : I ≃ J) : (I → Bool) ≃ (J → Bool) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem weight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : ℝ) (x : I → Bool) : weight p (assignmentEquiv e x) = weight p x := by
  unfold weight
  exact Fintype.prod_equiv e.symm _ _ (fun j => rfl)

theorem prob_equiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun y : J → Bool => E (fun i => y (e i))) = prob p E := by
  classical
  unfold prob
  rw [← Equiv.sum_comp (assignmentEquiv e)]
  apply sum_congr rfl
  intro x _
  have he : (fun i => assignmentEquiv e x (e i)) = x := by funext i; simp [assignmentEquiv]
  change (if E (fun i => assignmentEquiv e x (e i)) then weight p (assignmentEquiv e x) else 0) = _
  rw [he,weight_equiv]

theorem weight_product {I J : Type*} [Fintype I] [Fintype J]
    (p : ℝ) (x : I × J → Bool) :
    weight p x = ∏ i, weight p (fun j => x (i,j)) := by
  simp only [weight,Fintype.prod_prod_type]

theorem indicator_all {I : Type*} [Fintype I] (E : I → Bool) (w : I → ℝ) :
    (if (decide (∀ i, E i = true)) then ∏ i, w i else 0) =
      ∏ i, if E i then w i else 0 := by
  classical
  by_cases h : ∀ i, E i = true
  · simp [h]
  · have hz : ∃ i, E i = false := by simpa only [not_forall,Bool.not_eq_true] using h
    obtain ⟨i,hi⟩ := hz
    rw [if_neg (by simpa using h)]
    symm
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Disjoint blocks have independent acceptance events under product bias. -/
theorem prob_all_blocks {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (E : I → (J → Bool) → Bool) :
    prob p (fun x : I × J → Bool => decide (∀ i, E i (fun j => x (i,j)) = true)) =
      ∏ i, prob p (E i) := by
  classical
  unfold prob
  simp_rw [weight_product,indicator_all]
  rw [Fintype.sum_equiv (Equiv.curry I J Bool)
    (fun x : I × J → Bool => ∏ i, if E i (fun j => x (i,j)) then weight p (fun j => x (i,j)) else 0)
    (fun x : I → J → Bool => ∏ i, if E i (x i) then weight p (x i) else 0) (fun _ => rfl)]
  exact (Fintype.prod_sum (fun i : I => fun x : J → Bool => if E i x then weight p x else 0)).symm

theorem prob_all_copies {t m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p (fun x : Fin t × Fin m → Bool => decide (∀ i, E (fun j => x (i,j)) = true)) =
      bernProb p E ^ t := by
  convert (prob_all_blocks p (fun _ : Fin t => E)) using 1
  · congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  · simp only [prob_fin,prod_const,card_univ,Fintype.card_fin]

end SemAC02.BernoulliProduct
end

section
-- Inlined Solutions.ConjunctionCopies

set_option maxHeartbeats 1000000

open SemAC02.CircuitRenaming SemAC02.MonotoneCircuitPinning

namespace SemAC02.ConjunctionCopies

def children {V : Type} (t : ℕ) (cs : List (Circ V)) : List (Circ (Fin t × V)) :=
  (List.ofFn (fun i : Fin t => cs.map (Circ.rename (fun v => (i,v))))).flatten

open Classical in
noncomputable def amplify {V : Type} (t : ℕ) (cs : List (Circ V)) : Circ (Fin t × V) :=
  .and (children t cs).dedup

theorem mem_children {V : Type} {t : ℕ} {cs : List (Circ V)} {c : Circ (Fin t × V)} :
    c ∈ children t cs ↔ ∃ i : Fin t, ∃ a ∈ cs, a.rename (fun v => (i,v)) = c := by
  simp [children]

theorem monotone_amplify {V : Type} (t : ℕ) {cs : List (Circ V)}
    (hC : IsMonotoneCirc (.and cs)) : IsMonotoneCirc (amplify t cs) := by
  classical
  cases hC with
  | and _ hcs =>
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨i,a,ha,rfl⟩ := mem_children.mp (List.mem_dedup.mp hc)
    exact monotone_rename (fun v => (i,v)) (hcs a ha)

theorem reduced_amplify {V : Type} [Nonempty V] (t : ℕ) {cs : List (Circ V)}
    (hC : IsReduced (.and cs)) : IsReduced (amplify t cs) := by
  classical
  cases hC with
  | and _ hn ht hr =>
    apply IsReduced.and
    · exact List.nodup_dedup _
    · intro c hc
      obtain ⟨i,a,ha,rfl⟩ := mem_children.mp (List.mem_dedup.mp hc)
      simpa only [isAnd_rename] using ht a ha
    · intro c hc
      obtain ⟨i,a,ha,rfl⟩ := mem_children.mp (List.mem_dedup.mp hc)
      exact reduced_rename (fun v => (i,v)) (fun a b h => Prod.mk.inj h |>.2) (hr a ha)

theorem eval_amplify {V : Type} (t : ℕ) (cs : List (Circ V)) (x : Fin t × V → Bool) :
    (amplify t cs).eval x = decide (∀ i : Fin t, (Circ.and cs).eval (fun v => x (i,v)) = true) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [amplify,Circ.eval,List.all_map,all_dedup,Bool.decide_iff,List.all_eq_true]
  constructor
  · intro h i
    intro c hc
    have he := h (c.rename (fun v => (i,v))) (mem_children.mpr ⟨i,c,hc,rfl⟩)
    simpa only [eval_rename,Function.comp_def] using he
  · intro h c hc
    obtain ⟨i,a,ha,rfl⟩ := mem_children.mp hc
    simpa only [eval_rename,Function.comp_def] using h i a ha

theorem depth_amplify {V : Type} (t : ℕ) (cs : List (Circ V)) :
    (amplify t cs).depth ≤ (Circ.and cs).depth := by
  classical
  simp only [amplify,Circ.depth]
  apply Nat.add_le_add_left
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hk
  obtain ⟨i,a,ha,rfl⟩ := mem_children.mp (List.mem_dedup.mp hc)
  rw [depth_rename]
  exact List.le_max_of_le (List.mem_map.mpr ⟨a,ha,rfl⟩) le_rfl

theorem children_size {V : Type} (t : ℕ) (cs : List (Circ V)) :
    ((children t cs).map Circ.treeSize).sum = t * (cs.map Circ.treeSize).sum := by
  simp only [children,List.map_flatten,List.sum_flatten,List.map_ofFn,List.map_map,Function.comp_def]
  simp only [size_rename]
  simp

theorem size_amplify {V : Type} {t : ℕ} (ht : 1 ≤ t) (cs : List (Circ V)) :
    (amplify t cs).treeSize ≤ t * (Circ.and cs).treeSize := by
  classical
  have hs := dedup_sum_le (children t cs) Circ.treeSize
  rw [children_size] at hs
  simp only [amplify,Circ.treeSize]
  nlinarith

theorem prob_amplify {t m : ℕ} (p : ℝ) (cs : List (Circ (Fin m))) :
    BernoulliProduct.prob p (fun x => (amplify t cs).eval x) =
      bernProb p (fun x => (Circ.and cs).eval x) ^ t := by
  simp only [eval_amplify]
  exact BernoulliProduct.prob_all_copies (t := t) (m := m) p (fun x => (Circ.and cs).eval x)

end SemAC02.ConjunctionCopies
end

section
-- Inlined Solutions.ReadOnceLayers

set_option maxHeartbeats 1000000

open SemAC02.CircuitRenaming SemAC02.MonotoneCircuitPinning

namespace SemAC02.ReadOnceLayers

def siblings {V : Type} (t : ℕ) (C : Circ V) : List (Circ (Fin t × V)) :=
  List.ofFn (fun i : Fin t => C.rename (fun v => (i,v)))

open Classical in
noncomputable def andLayer {V : Type} (t : ℕ) (C : Circ V) : Circ (Fin t × V) :=
  .and (siblings t C).dedup

open Classical in
noncomputable def orLayer {V : Type} (t : ℕ) (C : Circ V) : Circ (Fin t × V) :=
  .or (siblings t C).dedup

theorem monotone_and {V : Type} (t : ℕ) {C : Circ V} (hC : IsMonotoneCirc C) :
    IsMonotoneCirc (andLayer t C) := by
  classical
  apply IsMonotoneCirc.and
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact monotone_rename _ hC

theorem monotone_or {V : Type} (t : ℕ) {C : Circ V} (hC : IsMonotoneCirc C) :
    IsMonotoneCirc (orLayer t C) := by
  classical
  apply IsMonotoneCirc.or
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact monotone_rename _ hC

theorem reduced_and {V : Type} [Nonempty V] (t : ℕ) {C : Circ V}
    (hC : IsReduced C) (hroot : C.isAnd = false) : IsReduced (andLayer t C) := by
  classical
  apply IsReduced.and
  · exact List.nodup_dedup _
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    simpa only [isAnd_rename] using hroot
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    exact reduced_rename (fun v => (i,v)) (fun a b h => Prod.mk.inj h |>.2) hC

theorem reduced_or {V : Type} [Nonempty V] (t : ℕ) {C : Circ V}
    (hC : IsReduced C) (hroot : C.isOr = false) : IsReduced (orLayer t C) := by
  classical
  apply IsReduced.or
  · exact List.nodup_dedup _
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    simpa only [isOr_rename] using hroot
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    exact reduced_rename (fun v => (i,v)) (fun a b h => Prod.mk.inj h |>.2) hC

theorem eval_and {V : Type} (t : ℕ) (C : Circ V) (x : Fin t × V → Bool) :
    (andLayer t C).eval x = decide (∀ i : Fin t, C.eval (fun v => x (i,v)) = true) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [andLayer,Circ.eval,List.all_map,all_dedup,siblings,eval_rename,Function.comp_def]

theorem eval_or {V : Type} (t : ℕ) (C : Circ V) (x : Fin t × V → Bool) :
    (orLayer t C).eval x = !(decide (∀ i : Fin t, (!C.eval (fun v => x (i,v))) = true)) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [orLayer,Circ.eval,List.any_map,any_dedup,siblings,eval_rename,Function.comp_def]

theorem depth_and {V : Type} (t : ℕ) (C : Circ V) : (andLayer t C).depth ≤ 1+C.depth := by
  classical
  simp only [andLayer,Circ.depth]
  apply Nat.add_le_add_left
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hk
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact (depth_rename _ C).le

theorem depth_or {V : Type} (t : ℕ) (C : Circ V) : (orLayer t C).depth ≤ 1+C.depth := by
  classical
  simp only [orLayer,Circ.depth]
  apply Nat.add_le_add_left
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hk
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact (depth_rename _ C).le

theorem siblings_size {V : Type} (t : ℕ) (C : Circ V) :
    ((siblings t C).map Circ.treeSize).sum = t*C.treeSize := by
  simp [siblings,List.map_ofFn,Function.comp_def,size_rename]

theorem size_and {V : Type} (t : ℕ) (C : Circ V) :
    (andLayer t C).treeSize ≤ 1+t*C.treeSize := by
  classical
  have hs := dedup_sum_le (siblings t C) Circ.treeSize
  rw [siblings_size] at hs
  simpa only [andLayer,Circ.treeSize] using Nat.add_le_add_left hs 1

theorem size_or {V : Type} (t : ℕ) (C : Circ V) :
    (orLayer t C).treeSize ≤ 1+t*C.treeSize := by
  classical
  have hs := dedup_sum_le (siblings t C) Circ.treeSize
  rw [siblings_size] at hs
  simpa only [orLayer,Circ.treeSize] using Nat.add_le_add_left hs 1

theorem prob_and {t m : ℕ} (p : ℝ) (C : Circ (Fin m)) :
    BernoulliProduct.prob p (fun x => (andLayer t C).eval x) =
      bernProb p (fun x => C.eval x) ^ t := by
  simp only [eval_and]
  exact BernoulliProduct.prob_all_copies (t := t) (m := m) p (fun x => C.eval x)

theorem prob_or {t m : ℕ} (p : ℝ) (C : Circ (Fin m)) :
    BernoulliProduct.prob p (fun x => (orLayer t C).eval x) =
      1-(1-bernProb p (fun x => C.eval x)) ^ t := by
  simp only [eval_or]
  rw [BernoulliProduct.prob_complement]
  have h := BernoulliProduct.prob_all_copies (t := t) (m := m) p (fun x => !C.eval x)
  rw [BernoulliAlgebra.prob_compl] at h
  rw [h]

end SemAC02.ReadOnceLayers
end

section
-- Inlined Solutions.CoinAlternatingLayers

set_option maxHeartbeats 1000000

open SemAC02.CircuitRenaming SemAC02.ReadOnceLayers SemAC02.BernoulliProduct

namespace SemAC02.CoinAlternatingLayers

/-- AND-rooted stages use acceptance as their rare event; OR-rooted stages use rejection. -/
def rareEvent {m : ℕ} (b : Bool) (C : Circ (Fin m)) (x : Fin m → Bool) : Bool :=
  if b then C.eval x else !C.eval x

@[simp] theorem rareEvent_true {m : ℕ} (C : Circ (Fin m)) :
    rareEvent true C = (fun x => C.eval x) := rfl
@[simp] theorem rareEvent_false {m : ℕ} (C : Circ (Fin m)) :
    rareEvent false C = (fun x => !C.eval x) := rfl

noncomputable def next {m : ℕ} (b : Bool) (C : Circ (Fin m)) (n : ℕ) : Circ (Fin (n*m)) :=
  (if b then orLayer n C else andLayer n C).rename finProdFinEquiv

theorem monotone_next {m : ℕ} (b : Bool) (C : Circ (Fin m)) (n : ℕ) (hC : IsMonotoneCirc C) :
    IsMonotoneCirc (next b C n) := by
  apply monotone_rename
  cases b
  · exact monotone_and n hC
  · exact monotone_or n hC

theorem reduced_next {m : ℕ} [Nonempty (Fin m)] (b : Bool) (C : Circ (Fin m)) (n : ℕ)
    (hn : 1 ≤ n) (hC : IsReduced C) (hA : C.isAnd = b) (hO : C.isOr = !b) :
    IsReduced (next b C n) := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  apply reduced_rename finProdFinEquiv finProdFinEquiv.injective
  cases b
  · exact reduced_and _ hC hA
  · exact reduced_or _ hC hO

theorem roots_next {m : ℕ} (b : Bool) (C : Circ (Fin m)) (n : ℕ) :
    (next b C n).isAnd = !b ∧ (next b C n).isOr = b := by
  cases b <;> simp [next,andLayer,orLayer,Circ.rename,Circ.isAnd,Circ.isOr]

theorem depth_next {m : ℕ} (b : Bool) (C : Circ (Fin m)) (n : ℕ) :
    (next b C n).depth ≤ 1+C.depth := by
  rw [next,depth_rename]
  cases b
  · exact depth_and n C
  · exact depth_or n C

theorem size_next {m : ℕ} (b : Bool) (C : Circ (Fin m)) (n : ℕ) :
    (next b C n).treeSize ≤ 1+n*C.treeSize := by
  rw [next,size_rename]
  cases b
  · exact size_and n C
  · exact size_or n C

theorem prob_next {m : ℕ} (p : ℝ) (b : Bool) (C : Circ (Fin m)) (n : ℕ) :
    bernProb p (rareEvent (!b) (next b C n)) =
      (1-bernProb p (rareEvent b C))^n := by
  have hrename (D : Circ (Fin n × Fin m)) :
      bernProb p (fun x => (D.rename finProdFinEquiv).eval x) = prob p (fun x => D.eval x) := by
    calc
      _ = prob p (fun x : Fin (n*m) → Bool => D.eval (fun v => x (finProdFinEquiv v))) := by
        simp only [prob_fin,eval_rename,Function.comp_def]
      _ = _ := prob_equiv finProdFinEquiv p (fun x => D.eval x)
  cases b
  · simp only [Bool.not_false,rareEvent_true,rareEvent_false,next,Bool.false_eq_true,↓reduceIte]
    rw [hrename,BernoulliAlgebra.prob_compl,prob_and]
    congr 1
    ring
  · simp only [Bool.not_true,rareEvent_true,rareEvent_false,next,Bool.false_eq_true,↓reduceIte]
    rw [BernoulliAlgebra.prob_compl,hrename,prob_or]
    ring

end SemAC02.CoinAlternatingLayers
end

section
-- Inlined Solutions.CoinDepthTwoNumerics

set_option maxHeartbeats 1000000

namespace SemAC02.CoinDepthTwoNumerics

theorem union_power_bound {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (r : ℕ) :
    1-(1-a)^r ≤ (r : ℝ)*a := by
  have h := one_add_mul_le_pow (a := -a) (by linarith : (-2 : ℝ) ≤ -a) r
  simp only [mul_neg,← sub_eq_add_neg] at h
  linarith

theorem failure_power_bound {a : ℝ} (ha : a ≤ 1) (r : ℕ) :
    (1-a)^r ≤ Real.exp (-((r : ℝ)*a)) := by
  calc
    _ ≤ Real.exp (-a)^r := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg a) r
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem exp_neg_tenth {a : ℝ} (ha : 9 ≤ a) : Real.exp (-a) ≤ 1/10 := by
  rw [Real.exp_neg]
  have he : 1/Real.exp a ≤ 1/10 := (div_le_iff₀ (Real.exp_pos a)).mpr (by linarith [Real.add_one_le_exp a])
  simpa only [one_div] using he

theorem depth_two_parameters {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ 11/ε ∧
      1-(1-((1-ε)/2)^m)^(2^m) ≤ 1/10 ∧
      (1-((1+ε)/2)^m)^(2^m) ≤ 1/10 ∧
      (1+(2^m)*(1+m) : ℕ) ≤ Real.exp (23*ε⁻¹) := by
  let m := ⌈10/ε⌉₊
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hml : 10/ε ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) < 10/ε+1 := Nat.ceil_lt_add_one (by positivity)
  have hmb : (m : ℝ) ≤ 11/ε := by
    have hle : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by linarith)
    calc
      (m : ℝ) ≤ 10/ε+1 := hmu.le
      _ ≤ 10/ε+1/ε := by linarith
      _ = 11/ε := by ring
  have hme : 10 ≤ (m : ℝ)*ε := (div_le_iff₀ hε).mp hml
  have hl : 0 ≤ (1-ε)/2 := by linarith
  have hlu : (1-ε)/2 ≤ 1 := by linarith
  have hh : 0 ≤ (1+ε)/2 := by linarith
  have hhu : (1+ε)/2 ≤ 1 := by linarith
  have hlowprod : ((2^m : ℕ) : ℝ)*((1-ε)/2)^m = (1-ε)^m := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  have hhighprod : ((2^m : ℕ) : ℝ)*((1+ε)/2)^m = (1+ε)^m := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  have hlow : 1-(1-((1-ε)/2)^m)^(2^m) ≤ 1/10 := by
    calc
      _ ≤ ((2^m : ℕ) : ℝ)*((1-ε)/2)^m :=
        union_power_bound (pow_nonneg hl m) (pow_le_one₀ hl hlu) _
      _ = (1-ε)^m := hlowprod
      _ ≤ Real.exp (-((m : ℝ)*ε)) := failure_power_bound hε'.le m
      _ ≤ 1/10 := exp_neg_tenth (by linarith)
  have hhigh : (1-((1+ε)/2)^m)^(2^m) ≤ 1/10 := by
    calc
      _ ≤ Real.exp (-(((2^m : ℕ) : ℝ)*((1+ε)/2)^m)) :=
        failure_power_bound (pow_le_one₀ hh hhu) _
      _ = Real.exp (-((1+ε)^m)) := by rw [hhighprod]
      _ ≤ 1/10 := exp_neg_tenth (by
        have h := one_add_mul_le_pow (a := ε) (by linarith : (-2 : ℝ) ≤ ε) m
        linarith)
  have htwo : (2 : ℝ)^m ≤ Real.exp (m : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) m
      _ = _ := by rw [← Real.exp_nat_mul,mul_one]
  have hlin : 1+(m : ℝ) ≤ Real.exp (m : ℝ) := by simpa only [add_comm] using Real.add_one_le_exp (m : ℝ)
  have hexp : 1 ≤ Real.exp (2*(m : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hsize : (1+(2^m)*(1+m) : ℕ) ≤ Real.exp (23*ε⁻¹) := by
    calc
      _ = 1+(2 : ℝ)^m*(1+(m : ℝ)) := by push_cast; rfl
      _ ≤ 1+Real.exp (m : ℝ)*Real.exp (m : ℝ) := by
        gcongr
      _ = 1+Real.exp (2*(m : ℝ)) := by rw [← Real.exp_add]; congr 2 <;> ring
      _ ≤ Real.exp 1*Real.exp (2*(m : ℝ)) := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
        nlinarith
      _ = Real.exp (1+2*(m : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (23*ε⁻¹) := by
        apply Real.exp_le_exp.mpr
        have hle : 1 ≤ ε⁻¹ := by
          have he : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by nlinarith)
          simpa only [one_div] using he
        simp only [div_eq_mul_inv] at hmb
        linarith
  exact ⟨m,hm,hmb,hlow,hhigh,hsize⟩

end SemAC02.CoinDepthTwoNumerics
end

section
-- Inlined Solutions.CoinLayerCalibration

set_option maxHeartbeats 1000000

namespace SemAC02.CoinLayerCalibration

noncomputable def fanIn (M p : ℝ) : ℕ := ⌈M/p⌉₊

theorem fanIn_pos {M p : ℝ} (hM : 0 < M) (hp : 0 < p) : 1 ≤ fanIn M p :=
  Nat.one_le_ceil_iff.mpr (div_pos hM hp)

theorem fanIn_scale_bounded {M p : ℝ} (hM : 0 < M) (hp : 0 < p) (hp' : p ≤ 1) :
    M ≤ (fanIn M p : ℝ)*p ∧ (fanIn M p : ℝ)*p ≤ M+1 := by
  have hl := Nat.le_ceil (M/p)
  have hu := Nat.ceil_lt_add_one (le_of_lt (div_pos hM hp))
  constructor
  · exact (div_le_iff₀ hp).mp hl
  · have h := mul_lt_mul_of_pos_right hu hp
    have he : (M/p+1)*p = M+p := by field_simp
    rw [he] at h
    exact h.le.trans (by linarith)

theorem log_one_sub_lower {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2) :
    -2*p ≤ Real.log (1-p) := by
  have hpos : 0 < 1-p := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hdiv : 1/(1-p) ≤ 1+2*p := (div_le_iff₀ hpos).mpr (by
    nlinarith [mul_nonneg hp (by linarith : 0 ≤ 1-2*p)])
  rw [one_div] at hdiv
  linarith

/-- One alternating layer restores a rare reference event to an exponential window. -/
theorem calibrated_window {M p : ℝ} (hM : 0 < M) (hp : 0 < p) (hp' : p ≤ 1/2) :
    Real.exp (-2*(M+1)) ≤ (1-p)^(fanIn M p) ∧
      (1-p)^(fanIn M p) ≤ Real.exp (-M) := by
  have hscale := fanIn_scale_bounded hM hp (by linarith)
  have hbase : 0 < 1-p := by linarith
  constructor
  · have hl := mul_le_mul_of_nonneg_left (log_one_sub_lower hp.le hp') (Nat.cast_nonneg (fanIn M p))
    have he : Real.exp ((fanIn M p : ℝ)*Real.log (1-p)) = (1-p)^(fanIn M p) := by
      rw [Real.exp_nat_mul,Real.exp_log hbase]
    rw [← he]
    apply Real.exp_le_exp.mpr
    nlinarith [hscale.2]
  · exact (CoinDepthTwoNumerics.failure_power_bound (by linarith : p ≤ 1) _).trans
      (Real.exp_le_exp.mpr (by linarith [hscale.1]))

theorem ordered_log_gap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p*(Real.log q-Real.log p) ≤ q-p := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at hl
  calc
    _ ≤ p*(q/p-1) := mul_le_mul_of_nonneg_left hl hp.le
    _ = _ := by field_simp

theorem weighted_log_gap {u p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hup : u ≤ p) (huq : u ≤ q) :
    u*|Real.log q-Real.log p| ≤ |q-p| := by
  rcases le_total p q with hpq | hqp
  · have hlog := Real.log_le_log hp hpq
    rw [abs_of_nonneg (sub_nonneg.mpr hlog),abs_of_nonneg (sub_nonneg.mpr hpq)]
    exact (mul_le_mul_of_nonneg_right hup (sub_nonneg.mpr hlog)).trans (ordered_log_gap hp hq)
  · have hlog := Real.log_le_log hq hqp
    rw [abs_of_nonpos (sub_nonpos.mpr hlog),abs_of_nonpos (sub_nonpos.mpr hqp)]
    have h := (mul_le_mul_of_nonneg_right huq (sub_nonneg.mpr hlog)).trans (ordered_log_gap hq hp)
    nlinarith

theorem log_gap_reference_lower {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hgap : |Real.log q-Real.log p| ≤ 10) :
    p*Real.exp (-10) ≤ p ∧ p*Real.exp (-10) ≤ q := by
  constructor
  · exact mul_le_of_le_one_right hp.le (Real.exp_le_one_iff.mpr (by norm_num))
  · have hlow := (abs_le.mp hgap).1
    have h := Real.exp_le_exp.mpr (show Real.log p+(-10) ≤ Real.log q from by linarith)
    simpa only [Real.exp_add,Real.exp_log hp,Real.exp_log hq] using h

theorem complement_log_gap {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hp' : p < 1) (hq' : q < 1) :
    |q-p| ≤ |Real.log (1-q)-Real.log (1-p)| := by
  have hordered : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 →
      b-a ≤ Real.log (1-a)-Real.log (1-b) := by
    intro a b ha hab hb
    have hapos : 0 < 1-a := by linarith
    have hbpos : 0 < 1-b := by linarith
    have hl := Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
    rw [Real.log_div hbpos.ne' hapos.ne'] at hl
    have hd : (1-b)/(1-a) ≤ 1-(b-a) := (div_le_iff₀ hapos).mpr (by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)])
    linarith
  rcases le_total p q with hpq | hqp
  · have hlog := Real.log_le_log (by linarith : 0 < 1-q) (by linarith : 1-q ≤ 1-p)
    rw [abs_of_nonneg (sub_nonneg.mpr hpq),abs_of_nonpos (sub_nonpos.mpr hlog)]
    linarith [hordered p q hp hpq hq']
  · have hlog := Real.log_le_log (by linarith : 0 < 1-p) (by linarith : 1-p ≤ 1-q)
    rw [abs_of_nonpos (sub_nonpos.mpr hqp),abs_of_nonneg (sub_nonneg.mpr hlog)]
    linarith [hordered q p hq hqp hp']

/-- Until the two rare-event probabilities separate by a fixed ratio, a layer amplifies their
logarithmic gap by a factor proportional to the scale M. -/
theorem calibrated_gap_growth {M p q : ℝ} (hM : 0 < M) (hp : 0 < p) (hq : 0 < q)
    (hp' : p < 1) (hq' : q < 1) (hgap : |Real.log q-Real.log p| ≤ 10) :
    M*Real.exp (-10)*|Real.log q-Real.log p| ≤
      |Real.log ((1-q)^(fanIn M p))-Real.log ((1-p)^(fanIn M p))| := by
  have hscale : M ≤ (fanIn M p : ℝ)*p := (div_le_iff₀ hp).mp (Nat.le_ceil (M/p))
  have href := log_gap_reference_lower hp hq hgap
  have hweighted := weighted_log_gap hp hq href.1 href.2
  have hcomp := complement_log_gap hp.le hq.le hp' hq'
  have hnon : 0 ≤ Real.exp (-10)*|Real.log q-Real.log p| := by positivity
  calc
    _ ≤ ((fanIn M p : ℝ)*p)*Real.exp (-10)*|Real.log q-Real.log p| := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hscale hnon
    _ = (fanIn M p : ℝ)*(p*Real.exp (-10)*|Real.log q-Real.log p|) := by ring
    _ ≤ (fanIn M p : ℝ)*|Real.log (1-q)-Real.log (1-p)| :=
      mul_le_mul_of_nonneg_left (hweighted.trans hcomp) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Real.log_pow,Real.log_pow,← mul_sub,abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ (fanIn M p : ℝ) from Nat.cast_nonneg _)]

theorem log_gap_reference_upper {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hgap : |Real.log q-Real.log p| ≤ 10) : q ≤ p*Real.exp 10 := by
  have hu := (abs_le.mp hgap).2
  have h := Real.exp_le_exp.mpr (show Real.log q ≤ Real.log p+10 from by linarith)
  simpa only [Real.exp_add,Real.exp_log hp,Real.exp_log hq] using h

theorem exp_neg_two_le_half : Real.exp (-2) ≤ 1/2 := by
  have h : 1/Real.exp 2 ≤ 1/2 := (div_le_iff₀ (Real.exp_pos 2)).mpr (by
    linarith [Real.add_one_le_exp 2])
  simpa only [Real.exp_neg,one_div] using h

theorem window_input_bounds {M p q : ℝ} (hM : 24 ≤ M) (hp : 0 < p) (hq : 0 < q)
    (hpu : p ≤ Real.exp (-M/2)) (hgap : |Real.log q-Real.log p| ≤ 10) :
    p ≤ 1/2 ∧ q ≤ 1/2 := by
  constructor
  · exact hpu.trans ((Real.exp_le_exp.mpr (by linarith : -M/2 ≤ -2)).trans exp_neg_two_le_half)
  · calc
      q ≤ p*Real.exp 10 := log_gap_reference_upper hp hq hgap
      _ ≤ Real.exp (-M/2)*Real.exp 10 := mul_le_mul_of_nonneg_right hpu (Real.exp_pos _).le
      _ = Real.exp (10-M/2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1/2 := exp_neg_two_le_half

/-- The calibrated fan-in contributes only an exponential factor to tree size. -/
theorem fanIn_size {M p : ℝ} (hM : 1 ≤ M) (hp : 0 < p)
    (hpl : Real.exp (-2*(M+1)) ≤ p) :
    1+(fanIn M p : ℝ) ≤ Real.exp (7*M) := by
  have hi : 1/p ≤ Real.exp (2*(M+1)) := by
    calc
      _ ≤ 1/Real.exp (-2*(M+1)) := one_div_le_one_div_of_le (Real.exp_pos _) hpl
      _ = _ := by rw [one_div,← Real.exp_neg]; congr 1; ring
  have hMu : M ≤ Real.exp M := by linarith [Real.add_one_le_exp M]
  have hpos : 0 < M := by linarith
  have hfan : (fanIn M p : ℝ) ≤ Real.exp (5*M)+1 := by
    have hf := Nat.ceil_lt_add_one (le_of_lt (div_pos hpos hp))
    apply hf.le.trans
    apply add_le_add _ le_rfl
    calc
      M/p = M*(1/p) := by ring
      _ ≤ M*Real.exp (2*(M+1)) := mul_le_mul_of_nonneg_left hi hpos.le
      _ ≤ Real.exp M*Real.exp (4*M) := by
        apply mul_le_mul hMu (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (5*M) := by rw [← Real.exp_add]; congr 1; ring
  have he5 : 1 ≤ Real.exp (5*M) := Real.one_le_exp_iff.mpr (by linarith)
  have he2 : 3 ≤ Real.exp (2*M) := by linarith [Real.add_one_le_exp (2*M)]
  have he : Real.exp (7*M) = Real.exp (2*M)*Real.exp (5*M) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith

theorem calibrated_positive {M p : ℝ} (hM : 0 < M) (hp : 0 < p) (hp' : p < 1) :
    0 < (1-p)^(fanIn M p) ∧ (1-p)^(fanIn M p) < 1 := by
  have hn := fanIn_pos hM hp
  exact ⟨pow_pos (by linarith) _,pow_lt_one₀ (by linarith) (by linarith) (by omega)⟩

end SemAC02.CoinLayerCalibration
end

section
-- Inlined Solutions.CoinReadOnceBaseNumerics

set_option maxHeartbeats 1000000

namespace SemAC02.CoinReadOnceBaseNumerics

theorem exp_neg_two_le_quarter : Real.exp (-2) ≤ 1/4 := by
  have htwo : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hfour : 4 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.exp_add]
    nlinarith
  have hi : 1/Real.exp 2 ≤ 1/4 := (div_le_iff₀ (Real.exp_pos 2)).mpr (by linarith)
  simpa only [Real.exp_neg,one_div] using hi

theorem base_window {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/2) (m : ℕ) :
    Real.exp (-2*((m : ℝ)+1)) ≤ ((1-ε)/2)^m ∧
      ((1-ε)/2)^m ≤ Real.exp (-(m : ℝ)/2) := by
  have hquarter : (1/4 : ℝ) ≤ (1-ε)/2 := by linarith
  constructor
  · calc
      _ ≤ Real.exp (-2*(m : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-2)^m := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ (1/4 : ℝ)^m := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_two_le_quarter m
      _ ≤ ((1-ε)/2)^m := pow_le_pow_left₀ (by norm_num) hquarter m
  · calc
      _ ≤ (1/2 : ℝ)^m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ Real.exp (-((m : ℝ)*(1/2))) := by
        convert (CoinDepthTwoNumerics.failure_power_bound (a := (1/2 : ℝ)) (by norm_num) m) using 1 <;> norm_num
      _ = _ := by congr 1; ring

theorem base_positive {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/2) {m : ℕ} (hm : 1 ≤ m) :
    0 < ((1-ε)/2)^m ∧ ((1-ε)/2)^m < 1 ∧
      0 < ((1+ε)/2)^m ∧ ((1+ε)/2)^m < 1 ∧ ((1-ε)/2)^m ≤ ((1+ε)/2)^m := by
  refine ⟨pow_pos (by linarith) _,pow_lt_one₀ (by linarith) (by linarith) (by omega),
    pow_pos (by linarith) _,pow_lt_one₀ (by linarith) (by linarith) (by omega),?_⟩
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

theorem base_gap {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/2) (m : ℕ) :
    ε*(m : ℝ) ≤ |Real.log (((1+ε)/2)^m)-Real.log (((1-ε)/2)^m)| := by
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1-ε from by linarith)
  have hh := Real.log_nonneg (show 1 ≤ 1+ε from by linarith)
  have hgap : ε ≤ Real.log ((1+ε)/2)-Real.log ((1-ε)/2) := by
    rw [Real.log_div (by linarith : (1+ε : ℝ) ≠ 0) (by norm_num),
      Real.log_div (by linarith : (1-ε : ℝ) ≠ 0) (by norm_num)]
    linarith
  calc
    _ = (m : ℝ)*ε := by ring
    _ ≤ (m : ℝ)*(Real.log ((1+ε)/2)-Real.log ((1-ε)/2)) :=
      mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg m)
    _ = Real.log (((1+ε)/2)^m)-Real.log (((1-ε)/2)^m) := by rw [Real.log_pow,Real.log_pow]; ring
    _ ≤ _ := le_abs_self _

end SemAC02.CoinReadOnceBaseNumerics
end

section
-- Inlined Solutions.CoinDepthTwo

set_option maxHeartbeats 1000000

open SemAC02.CircuitRenaming SemAC02.BernoulliProduct SemAC02.ReadOnceLayers

namespace SemAC02.CoinDepthTwo

def allInputs (m : ℕ) : Circ (Fin m) := .and (List.ofFn (fun j : Fin m => .lit j true))

theorem monotone_all (m : ℕ) : IsMonotoneCirc (allInputs m) := by
  apply IsMonotoneCirc.and
  intro c hc
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
  exact .lit j

theorem reduced_all (m : ℕ) : IsReduced (allInputs m) := by
  apply IsReduced.and
  · exact List.nodup_ofFn.mpr (fun a b h => Circ.lit.inj h |>.1)
  · intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    rfl
  · intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    exact .lit j true

theorem depth_all (m : ℕ) : (allInputs m).depth ≤ 1 := by
  rw [allInputs,Circ.depth]
  have hz : (List.map Circ.depth (List.ofFn (fun j : Fin m => .lit j true))).foldr max 0 ≤ 0 := by
    apply List.max_le_of_forall_le
    intro k hk
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hk
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    simp only [Circ.depth,le_refl]
  simpa only [Nat.add_zero] using Nat.add_le_add_left hz 1

theorem size_all (m : ℕ) : (allInputs m).treeSize = 1+m := by
  simp [allInputs,Circ.treeSize,List.map_ofFn,Function.comp_def]

theorem eval_all (m : ℕ) (x : Fin m → Bool) :
    (allInputs m).eval x = decide (∀ j, x j = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [allInputs,Circ.eval,List.all_map]

theorem prob_all (p : ℝ) (m : ℕ) : bernProb p (fun x => (allInputs m).eval x) = p^m := by
  change prob p (fun x => (allInputs m).eval x) = p^m
  simp only [eval_all]
  convert (prob_all_coordinates (I := Fin m) p) using 1
  · congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  · simp

/-- The depth-two instance of the coin-formula bound, with explicit exponent constant 23. -/
theorem coin_depth_two :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ 2 ∧
        (T.treeSize : ℝ) ≤ Real.exp (A*ε⁻¹) ∧
        IsCoinDistinguisher ε (1/10) (fun x => T.eval x) := by
  classical
  refine ⟨23,1,by norm_num,?_⟩
  intro ε hε hε'
  obtain ⟨m,hm,hmb,hlo,hhi,hsize⟩ := CoinDepthTwoNumerics.depth_two_parameters hε hε'
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let r := 2^m
  let C := orLayer r (allInputs m)
  let e : Fin r × Fin m ≃ Fin (r*m) := finProdFinEquiv
  let T := C.rename e
  have hprob (p : ℝ) : bernProb p (fun x => T.eval x) = 1-(1-p^m)^r := by
    calc
      _ = prob p (fun x : Fin (r*m) → Bool => C.eval (fun v => x (e v))) := by
        simp only [prob_fin,T,eval_rename,Function.comp_def]
      _ = prob p (fun x => C.eval x) := prob_equiv e p (fun x => C.eval x)
      _ = 1-(1-bernProb p (fun x => (allInputs m).eval x))^r := prob_or p _
      _ = _ := by rw [prob_all]
  have hM := monotone_or r (monotone_all m)
  have hR := reduced_or r (reduced_all m) (show (allInputs m).isOr = false from rfl)
  refine ⟨r*m,T,monotone_rename e hM,reduced_rename e e.injective hR,?_,?_,?_,?_⟩
  · exact (depth_rename e C).le.trans ((depth_or r (allInputs m)).trans (by have := depth_all m; omega))
  · have hs : (T.treeSize : ℝ) ≤ ((1+r*(1+m) : ℕ) : ℝ) := by
      dsimp only [T]
      rw [size_rename]
      exact_mod_cast (size_or r (allInputs m)).trans (by rw [size_all])
    exact hs.trans hsize
  · rw [hprob]
    exact hlo
  · rw [BernoulliAlgebra.prob_compl,hprob]
    convert hhi using 1 <;> ring

end SemAC02.CoinDepthTwo
end

section
-- Inlined Solutions.CoinReadOnceStages

set_option maxHeartbeats 1000000

open SemAC02.CoinAlternatingLayers SemAC02.CoinLayerCalibration

namespace SemAC02.CoinReadOnceStages

structure Stage (ε : ℝ) (M k : ℕ) where
  inputs : ℕ
  inputs_pos : 1 ≤ inputs
  C : Circ (Fin inputs)
  b : Bool
  p : ℝ
  q : ℝ
  monotone : IsMonotoneCirc C
  reduced : IsReduced C
  root_and : C.isAnd = b
  root_or : C.isOr = !b
  depth_le : C.depth ≤ k+1
  size_le : (C.treeSize : ℝ) ≤ Real.exp ((1+7*(k : ℝ))*(M : ℝ))
  p_eq : bernProb ((1-ε)/2) (rareEvent b C) = p
  q_eq : bernProb ((1+ε)/2) (rareEvent b C) = q
  p_pos : 0 < p
  p_lt_one : p < 1
  q_pos : 0 < q
  q_lt_one : q < 1
  p_lower : Real.exp (-2*((M : ℝ)+1)) ≤ p
  p_upper : p ≤ Real.exp (-(M : ℝ)/2)
  ordered : if b then p ≤ q else q ≤ p
  gap_lower : min 10 (ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k) ≤ |Real.log q-Real.log p|

theorem treeSize_pos {V : Type} (C : Circ V) : 1 ≤ C.treeSize := by
  cases C <;> simp only [Circ.treeSize] <;> omega

noncomputable def initial {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/2) (M : ℕ) (hM : 1 ≤ M) :
    Stage ε M 0 where
  inputs := M
  inputs_pos := hM
  C := CoinDepthTwo.allInputs M
  b := true
  p := ((1-ε)/2)^M
  q := ((1+ε)/2)^M
  monotone := CoinDepthTwo.monotone_all M
  reduced := CoinDepthTwo.reduced_all M
  root_and := rfl
  root_or := rfl
  depth_le := CoinDepthTwo.depth_all M
  size_le := by
    rw [CoinDepthTwo.size_all]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,mul_zero,add_zero,one_mul]
    linarith [Real.add_one_le_exp (M : ℝ)]
  p_eq := by rw [rareEvent_true,CoinDepthTwo.prob_all]
  q_eq := by rw [rareEvent_true,CoinDepthTwo.prob_all]
  p_pos := (CoinReadOnceBaseNumerics.base_positive hε hε' hM).1
  p_lt_one := (CoinReadOnceBaseNumerics.base_positive hε hε' hM).2.1
  q_pos := (CoinReadOnceBaseNumerics.base_positive hε hε' hM).2.2.1
  q_lt_one := (CoinReadOnceBaseNumerics.base_positive hε hε' hM).2.2.2.1
  p_lower := (CoinReadOnceBaseNumerics.base_window hε hε' M).1
  p_upper := (CoinReadOnceBaseNumerics.base_window hε hε' M).2
  ordered := (CoinReadOnceBaseNumerics.base_positive hε hε' hM).2.2.2.2
  gap_lower := by
    simp only [pow_zero,mul_one]
    exact (min_le_right _ _).trans (CoinReadOnceBaseNumerics.base_gap hε hε' M)

end SemAC02.CoinReadOnceStages
end

section
-- Inlined Solutions.CoinReadOnceIteration

set_option maxHeartbeats 2000000

open SemAC02.CoinAlternatingLayers SemAC02.CoinLayerCalibration

namespace SemAC02.CoinReadOnceStages

noncomputable def hold {ε : ℝ} {M k : ℕ} (S : Stage ε M k)
    (hgap : 10 ≤ |Real.log S.q-Real.log S.p|) : Stage ε M (k+1) where
  inputs := S.inputs
  inputs_pos := S.inputs_pos
  C := S.C
  b := S.b
  p := S.p
  q := S.q
  monotone := S.monotone
  reduced := S.reduced
  root_and := S.root_and
  root_or := S.root_or
  depth_le := by have := S.depth_le; omega
  size_le := S.size_le.trans (Real.exp_le_exp.mpr (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) M]))
  p_eq := S.p_eq
  q_eq := S.q_eq
  p_pos := S.p_pos
  p_lt_one := S.p_lt_one
  q_pos := S.q_pos
  q_lt_one := S.q_lt_one
  p_lower := S.p_lower
  p_upper := S.p_upper
  ordered := S.ordered
  gap_lower := (min_le_left _ _).trans hgap

noncomputable def advance {ε : ℝ} {M k : ℕ} (hM : 24 ≤ M) (S : Stage ε M k)
    (hgap : |Real.log S.q-Real.log S.p| < 10) : Stage ε M (k+1) := by
  classical
  have hMr : (24 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by linarith
  let n := fanIn (M : ℝ) S.p
  have hn : 1 ≤ n := fanIn_pos hMpos S.p_pos
  letI : Nonempty (Fin S.inputs) := ⟨⟨0,by have := S.inputs_pos; omega⟩⟩
  let T := next S.b S.C n
  have hroot := roots_next S.b S.C n
  have hinputs := window_input_bounds hMr S.p_pos S.q_pos S.p_upper hgap.le
  have hwindow := calibrated_window hMpos S.p_pos hinputs.1
  have hsize : (T.treeSize : ℝ) ≤ Real.exp ((1+7*((k+1 : ℕ) : ℝ))*(M : ℝ)) := by
    have hs : (T.treeSize : ℝ) ≤ 1+(n : ℝ)*(S.C.treeSize : ℝ) := by
      exact_mod_cast size_next S.b S.C n
    have hc : 1 ≤ (S.C.treeSize : ℝ) := by exact_mod_cast treeSize_pos S.C
    calc
      _ ≤ 1+(n : ℝ)*(S.C.treeSize : ℝ) := hs
      _ ≤ (1+(n : ℝ))*(S.C.treeSize : ℝ) := by nlinarith
      _ ≤ Real.exp (7*(M : ℝ))*Real.exp ((1+7*(k : ℝ))*(M : ℝ)) :=
        mul_le_mul (fanIn_size (by linarith : 1 ≤ (M : ℝ)) S.p_pos S.p_lower) S.size_le
          (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring
  have hraw : ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k ≤ |Real.log S.q-Real.log S.p| := by
    have ha : ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k < 10 :=
      (min_lt_iff.mp (S.gap_lower.trans_lt hgap)).resolve_left (lt_irrefl _)
    simpa only [min_eq_right ha.le] using S.gap_lower
  have hgrowth := calibrated_gap_growth hMpos S.p_pos S.q_pos S.p_lt_one S.q_lt_one hgap.le
  refine {
    inputs := n*S.inputs
    inputs_pos := by have := S.inputs_pos; nlinarith
    C := T
    b := !S.b
    p := (1-S.p)^n
    q := (1-S.q)^n
    monotone := monotone_next S.b S.C n S.monotone
    reduced := reduced_next S.b S.C n hn S.reduced S.root_and S.root_or
    root_and := hroot.1
    root_or := by simpa only [Bool.not_not] using hroot.2
    depth_le := (depth_next S.b S.C n).trans (by have := S.depth_le; omega)
    size_le := hsize
    p_eq := by rw [prob_next,S.p_eq]
    q_eq := by rw [prob_next,S.q_eq]
    p_pos := pow_pos (by linarith [S.p_lt_one]) _
    p_lt_one := pow_lt_one₀ (by linarith [S.p_lt_one]) (by linarith [S.p_pos]) (by omega)
    q_pos := pow_pos (by linarith [S.q_lt_one]) _
    q_lt_one := pow_lt_one₀ (by linarith [S.q_lt_one]) (by linarith [S.q_pos]) (by omega)
    p_lower := hwindow.1
    p_upper := hwindow.2.trans (Real.exp_le_exp.mpr (by linarith))
    ordered := ?_
    gap_lower := ?_
  }
  · cases hb : S.b
    · have ho : S.q ≤ S.p := by simpa only [hb,Bool.false_eq_true,↓reduceIte] using S.ordered
      simpa only [hb,Bool.not_false,↓reduceIte] using
        (pow_le_pow_left₀ (by linarith [S.p_lt_one] : 0 ≤ 1-S.p) (by linarith : 1-S.p ≤ 1-S.q) n)
    · have ho : S.p ≤ S.q := by simpa only [hb,↓reduceIte] using S.ordered
      simpa only [hb,Bool.not_true,Bool.false_eq_true,↓reduceIte] using
        (pow_le_pow_left₀ (by linarith [S.q_lt_one] : 0 ≤ 1-S.q) (by linarith : 1-S.q ≤ 1-S.p) n)
  · apply (min_le_right _ _).trans
    calc
      ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^(k+1) =
          ((M : ℝ)*Real.exp (-10))*(ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k) := by rw [pow_succ]; ring
      _ ≤ ((M : ℝ)*Real.exp (-10))*|Real.log S.q-Real.log S.p| :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ _ := hgrowth

theorem stage_exists {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/2) (M : ℕ) (hM : 24 ≤ M) (k : ℕ) :
    Nonempty (Stage ε M k) := by
  induction k with
  | zero => exact ⟨initial hε hε' M (by omega)⟩
  | succ k ih =>
    obtain ⟨S⟩ := ih
    by_cases hg : 10 ≤ |Real.log S.q-Real.log S.p|
    · exact ⟨hold S hg⟩
    · exact ⟨advance hM S (lt_of_not_ge hg)⟩

end SemAC02.CoinReadOnceStages
end

section
-- Inlined Solutions.CoinFinalAmplificationNumerics

set_option maxHeartbeats 1000000

open SemAC02.CoinLayerCalibration

namespace SemAC02.CoinFinalAmplificationNumerics

theorem exp_ten_large : 1024 ≤ Real.exp 10 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 10
  norm_num only [show (2 : ℝ)^10 = 1024 by norm_num] at hp
  simpa only [← Real.exp_nat_mul,mul_one,Nat.cast_ofNat] using hp

theorem small_error : 11*Real.exp (-10) ≤ 1/10 := by
  rw [Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos 10)).mpr
  linarith [exp_ten_large]

theorem gap_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hgap : 10 ≤ |Real.log q-Real.log p|) : p ≤ q*Real.exp (-10) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hp hpq))] at hgap
  have h := Real.exp_le_exp.mpr (show Real.log p ≤ Real.log q+(-10) from by linarith)
  simpa only [Real.exp_add,Real.exp_log hp,Real.exp_log hq] using h

theorem separated_errors {a b : ℝ} (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 ≤ b)
    (hab : b ≤ a*Real.exp (-10)) :
    (1-a)^(fanIn 10 a) ≤ 1/10 ∧ 1-(1-b)^(fanIn 10 a) ≤ 1/10 := by
  have hs := fanIn_scale_bounded (by norm_num : (0 : ℝ) < 10) ha ha'
  have hb' : b ≤ 1 := hab.trans ((mul_le_of_le_one_right ha.le
    (Real.exp_le_one_iff.mpr (by norm_num))).trans ha')
  constructor
  · exact (CoinDepthTwoNumerics.failure_power_bound ha' _).trans
      (CoinDepthTwoNumerics.exp_neg_tenth (by linarith [hs.1]))
  · calc
      _ ≤ (fanIn 10 a : ℝ)*b := CoinDepthTwoNumerics.union_power_bound hb hb' _
      _ ≤ (fanIn 10 a : ℝ)*(a*Real.exp (-10)) :=
        mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
      _ = ((fanIn 10 a : ℝ)*a)*Real.exp (-10) := by ring
      _ ≤ 11*Real.exp (-10) := mul_le_mul_of_nonneg_right (by linarith [hs.2] : (fanIn 10 a : ℝ)*a ≤ 11) (Real.exp_pos _).le
      _ ≤ _ := small_error

theorem final_fanIn_le {M p a : ℝ} (hM : 10 ≤ M) (hp : 0 < p) (ha : 0 < a) (hpa : p ≤ a) :
    fanIn 10 a ≤ fanIn M p := by
  apply Nat.ceil_le_ceil
  apply (div_le_div_iff₀ ha hp).mpr
  have h1 := mul_le_mul_of_nonneg_left hpa (show 0 ≤ M from by linarith)
  have h2 := mul_le_mul_of_nonneg_right hM hp.le
  nlinarith

end SemAC02.CoinFinalAmplificationNumerics
end

section
-- Inlined Solutions.CoinReadOnceFinish

set_option maxHeartbeats 2000000

open SemAC02.CoinAlternatingLayers SemAC02.CoinLayerCalibration
open SemAC02.CoinFinalAmplificationNumerics

namespace SemAC02.CoinReadOnceStages

theorem finish {ε : ℝ} {M k : ℕ} (hM : 24 ≤ M) (S : Stage ε M k)
    (hgap : 10 ≤ |Real.log S.q-Real.log S.p|) :
    ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ k+2 ∧
      (T.treeSize : ℝ) ≤ Real.exp ((8+7*(k : ℝ))*(M : ℝ)) ∧
      IsCoinDistinguisher ε (1/10) (fun x => T.eval x) := by
  classical
  have hMr : (24 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  let a := if S.b then S.q else S.p
  let small := if S.b then S.p else S.q
  have ha : 0 < a := by dsimp [a]; split <;> first | exact S.q_pos | exact S.p_pos
  have ha' : a ≤ 1 := by dsimp [a]; split <;> first | exact S.q_lt_one.le | exact S.p_lt_one.le
  have hb : 0 ≤ small := by dsimp [small]; split <;> first | exact S.p_pos.le | exact S.q_pos.le
  have hpa : S.p ≤ a := by
    cases ht : S.b
    · simp only [a,ht,Bool.false_eq_true,↓reduceIte,le_refl]
    · simpa only [a,ht,↓reduceIte] using S.ordered
  have hratio : small ≤ a*Real.exp (-10) := by
    cases ht : S.b
    · have ho : S.q ≤ S.p := by simpa only [ht,Bool.false_eq_true,↓reduceIte] using S.ordered
      simpa only [a,small,ht,Bool.false_eq_true,↓reduceIte] using
        gap_ratio S.q_pos S.p_pos ho (by simpa only [abs_sub_comm] using hgap)
    · have ho : S.p ≤ S.q := by simpa only [ht,↓reduceIte] using S.ordered
      simpa only [a,small,ht,↓reduceIte] using gap_ratio S.p_pos S.q_pos ho hgap
  let n := fanIn 10 a
  have hn : 1 ≤ n := fanIn_pos (by norm_num) ha
  have hnle : n ≤ fanIn (M : ℝ) S.p := final_fanIn_le (by linarith) S.p_pos ha hpa
  letI : Nonempty (Fin S.inputs) := ⟨⟨0,by have := S.inputs_pos; omega⟩⟩
  let T := next S.b S.C n
  have hlo : bernProb ((1-ε)/2) (rareEvent (!S.b) T) = (1-S.p)^n := by rw [prob_next,S.p_eq]
  have hhi : bernProb ((1+ε)/2) (rareEvent (!S.b) T) = (1-S.q)^n := by rw [prob_next,S.q_eq]
  have herr := separated_errors ha ha' hb hratio
  have hcoin : IsCoinDistinguisher ε (1/10) (fun x => T.eval x) := by
    cases ht : S.b
    · have he : (1-S.p)^n ≤ 1/10 ∧ 1-(1-S.q)^n ≤ 1/10 := by
        simpa only [n,a,small,ht,Bool.false_eq_true,↓reduceIte] using herr
      simp only [ht,Bool.not_false,rareEvent_true] at hlo hhi
      constructor
      · exact hlo.le.trans he.1
      · rw [BernoulliAlgebra.prob_compl,hhi]
        exact he.2
    · have he : (1-S.q)^n ≤ 1/10 ∧ 1-(1-S.p)^n ≤ 1/10 := by
        simpa only [n,a,small,ht,↓reduceIte] using herr
      simp only [ht,Bool.not_true,rareEvent_false] at hlo hhi
      constructor
      · rw [BernoulliAlgebra.prob_compl] at hlo
        linarith [he.2]
      · exact hhi.le.trans he.1
  refine ⟨n*S.inputs,T,monotone_next S.b S.C n S.monotone,
    reduced_next S.b S.C n hn S.reduced S.root_and S.root_or,?_,?_,hcoin⟩
  · exact (depth_next S.b S.C n).trans (by have := S.depth_le; omega)
  · have hs : (T.treeSize : ℝ) ≤ 1+(n : ℝ)*(S.C.treeSize : ℝ) := by
      exact_mod_cast size_next S.b S.C n
    have hc : 1 ≤ (S.C.treeSize : ℝ) := by exact_mod_cast treeSize_pos S.C
    have hncast : (n : ℝ) ≤ (fanIn (M : ℝ) S.p : ℝ) := by exact_mod_cast hnle
    have hfactor : 1+(n : ℝ) ≤ Real.exp (7*(M : ℝ)) := by
      have hf := fanIn_size (by linarith : 1 ≤ (M : ℝ)) S.p_pos S.p_lower
      linarith
    calc
      _ ≤ 1+(n : ℝ)*(S.C.treeSize : ℝ) := hs
      _ ≤ (1+(n : ℝ))*(S.C.treeSize : ℝ) := by nlinarith
      _ ≤ Real.exp (7*(M : ℝ))*Real.exp ((1+7*(k : ℝ))*(M : ℝ)) :=
        mul_le_mul hfactor S.size_le (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SemAC02.CoinReadOnceStages
end

section
-- Inlined Solutions.CoinReadOnceParameters

set_option maxHeartbeats 1000000

namespace SemAC02.CoinReadOnceParameters

noncomputable def scaleConstant (k : ℕ) : ℝ := 24+10*Real.exp (10*(k : ℝ))

theorem constant_bounds (k : ℕ) : 24 ≤ scaleConstant k ∧ 10*Real.exp (10*(k : ℝ)) ≤ scaleConstant k := by
  unfold scaleConstant
  constructor <;> linarith [Real.exp_pos (10*(k : ℝ))]

theorem scale_power {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    (ε^(-1/((k+1 : ℕ) : ℝ)))^(k+1) = ε⁻¹ := by
  rw [← Real.rpow_mul_natCast hε.le]
  have hn : (((k+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (-1/((k+1 : ℕ) : ℝ))*((k+1 : ℕ) : ℝ) = -1 by field_simp]
  exact Real.rpow_neg_one ε

theorem scale_ge_one {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) (k : ℕ) :
    1 ≤ ε^(-1/((k+1 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have he : -1/((k+1 : ℕ) : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hn.le
  simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos hε hε' he

theorem choose_scale {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) (k : ℕ) :
    ∃ M : ℕ, 24 ≤ M ∧
      (M : ℝ) ≤ (scaleConstant k+1)*ε^(-1/((k+1 : ℕ) : ℝ)) ∧
      10 ≤ ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k := by
  let B := scaleConstant k
  let L := ε^(-1/((k+1 : ℕ) : ℝ))
  let M := ⌈B*L⌉₊
  have hB24 : 24 ≤ B := (constant_bounds k).1
  have hB1 : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hL1 : 1 ≤ L := scale_ge_one hε hε' k
  have hLpos : 0 < L := by linarith
  have hMlo : B*L ≤ (M : ℝ) := Nat.le_ceil _
  have hM24 : (24 : ℝ) ≤ (M : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hL1 hBpos.le
    linarith
  have hMhi : (M : ℝ) ≤ (B+1)*L := by
    have hu := Nat.ceil_lt_add_one (mul_nonneg hBpos.le hLpos.le)
    nlinarith
  have hpower : B^(k+1) ≤ ε*(M : ℝ)^(k+1) := by
    have hp := pow_le_pow_left₀ (mul_nonneg hBpos.le hLpos.le) hMlo (k+1)
    have he := mul_le_mul_of_nonneg_left hp hε.le
    rw [mul_pow,show L^(k+1) = ε⁻¹ from scale_power hε k] at he
    have hc : ε*(B^(k+1)*ε⁻¹) = B^(k+1) := by field_simp
    rw [hc] at he
    exact he
  have hcancel : Real.exp (10*(k : ℝ))*(Real.exp (-10))^k = 1 := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hgrowth : 10 ≤ ε*(M : ℝ)*((M : ℝ)*Real.exp (-10))^k := by
    calc
      10 = (10*Real.exp (10*(k : ℝ)))*(Real.exp (-10))^k := by rw [mul_assoc,hcancel,mul_one]
      _ ≤ B*(Real.exp (-10))^k := mul_le_mul_of_nonneg_right (constant_bounds k).2 (by positivity)
      _ ≤ B^(k+1)*(Real.exp (-10))^k :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ hB1 (by omega)) (by positivity)
      _ ≤ (ε*(M : ℝ)^(k+1))*(Real.exp (-10))^k := mul_le_mul_of_nonneg_right hpower (by positivity)
      _ = _ := by rw [mul_pow,pow_succ]; ring
  exact ⟨M,by exact_mod_cast hM24,hMhi,hgrowth⟩

end SemAC02.CoinReadOnceParameters
end

section
-- Inlined Solutions.CoinFormulas

set_option maxHeartbeats 2000000

open SemAC02.CoinReadOnceStages SemAC02.CoinReadOnceParameters

namespace SemAC02.CoinFormulas

theorem coin_formulas (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A*ε^(-1/((d : ℝ)-1))) ∧
        IsCoinDistinguisher ε (1/10) (fun x => T.eval x) := by
  classical
  let k := d-2
  let B := scaleConstant k
  refine ⟨(8+7*(k : ℝ))*(B+1),1/2,by norm_num,?_⟩
  intro ε hε hε'
  obtain ⟨M,hM,hMsize,hgrowth⟩ := choose_scale hε (by linarith : ε ≤ 1) k
  obtain ⟨S⟩ := stage_exists hε hε' M hM k
  have hgap : 10 ≤ |Real.log S.q-Real.log S.p| := by
    have h := S.gap_lower
    rw [min_eq_left hgrowth] at h
    exact h
  obtain ⟨m,T,hmon,hred,hdepth,hsize,hcoin⟩ := finish hM S hgap
  refine ⟨m,T,hmon,hred,?_,?_,hcoin⟩
  · have hk : k+2 = d := by dsimp [k]; omega
    simpa only [hk] using hdepth
  · have hk : k+1 = d-1 := by dsimp [k]; omega
    have hden : ((k+1 : ℕ) : ℝ) = (d : ℝ)-1 := by
      rw [hk,Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
    rw [hden] at hMsize
    apply hsize.trans
    apply Real.exp_le_exp.mpr
    calc
      (8+7*(k : ℝ))*(M : ℝ) ≤ (8+7*(k : ℝ))*((B+1)*ε^(-1/((d : ℝ)-1))) :=
        mul_le_mul_of_nonneg_left hMsize (by positivity)
      _ = _ := by ring

end SemAC02.CoinFormulas
end

open SemAC02

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        IsCoinDistinguisher ε (1 / 10) (fun x => T.eval x)  := by
  exact SemAC02.CoinFormulas.coin_formulas d hd
