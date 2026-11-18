-- Prove2me | solution 1 for SemAC02.lemma_8_12_covering_gadget
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T21:16:33.615297+00:00
-- url     : https://prove2.me/submissions/bfc69c83-1451-4706-873f-9ba04109e2db

import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb
import Mathlib
import Definitions.Def_SemAC02_IsCoinDistinguisher

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
-- Inlined Solutions.MonotoneCircuitRelabeling

open SemAC02.MonotoneCircuitPinning

set_option maxHeartbeats 1000000

namespace SemAC02.MonotoneCircuitRelabeling

open Classical in
noncomputable def relabel {V W : Type} (f : V → W) : Circ V → Circ W
  | .const b => .const b
  | .lit v b => .lit (f v) b
  | .and cs => .and (cs.map (relabel f)).dedup
  | .or cs => .or (cs.map (relabel f)).dedup
  | .xor cs => .xor (cs.map (relabel f))

@[simp] theorem isAnd_relabel {V W : Type} (f : V → W) (C : Circ V) : (relabel f C).isAnd = C.isAnd := by
  cases C with
  | const b => simp only [relabel,Circ.isAnd]
  | lit v b => rw [relabel]; rfl
  | and cs => rw [relabel]; rfl
  | or cs => rw [relabel]; rfl
  | xor cs => rw [relabel]; rfl

@[simp] theorem isOr_relabel {V W : Type} (f : V → W) (C : Circ V) : (relabel f C).isOr = C.isOr := by
  cases C with
  | const b => simp only [relabel,Circ.isOr]
  | lit v b => rw [relabel]; rfl
  | and cs => rw [relabel]; rfl
  | or cs => rw [relabel]; rfl
  | xor cs => rw [relabel]; rfl

theorem monotone_relabel {V W : Type} (f : V → W) {C : Circ V} (hC : IsMonotoneCirc C) : IsMonotoneCirc (relabel f C) := by
  classical
  induction hC with
  | const b => rw [relabel]; exact .const _
  | lit v => rw [relabel]; constructor
  | and cs hcs ih =>
    rw [relabel]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
    exact ih c' hc'
  | or cs hcs ih =>
    rw [relabel]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
    exact ih c' hc'

theorem reduced_relabel {V W : Type} (f : V → W) {C : Circ V}
    (hC : IsMonotoneCirc C) (hR : IsReduced C) : IsReduced (relabel f C) := by
  classical
  induction hC with
  | const b => rw [relabel]; exact .const _
  | lit v => rw [relabel]; constructor
  | and cs hcs ih =>
    cases hR with
    | and _ _ htype hred =>
      rw [relabel]
      apply IsReduced.and
      · exact List.nodup_dedup _
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        simpa only [isAnd_relabel] using htype c' hc'
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        exact ih c' hc' (hred c' hc')
  | or cs hcs ih =>
    cases hR with
    | or _ _ htype hred =>
      rw [relabel]
      apply IsReduced.or
      · exact List.nodup_dedup _
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        simpa only [isOr_relabel] using htype c' hc'
      · intro c hc
        obtain ⟨c',hc',rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
        exact ih c' hc' (hred c' hc')

theorem eval_relabel {V W : Type} (f : V → W) {C : Circ V} (hC : IsMonotoneCirc C) (x : W → Bool) :
    (relabel f C).eval x = C.eval (x ∘ f) := by
  classical
  induction hC with
  | const b => simp only [relabel,Circ.eval]
  | lit v => simp only [relabel,Circ.eval,Function.comp_def]
  | and cs hcs ih =>
    have he : cs.map (fun c => (relabel f c).eval x) = cs.map (fun c => c.eval (x ∘ f)) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [relabel,Circ.eval,List.all_map,all_dedup,Function.comp_def]
    simpa only [List.all_map,Function.comp_def] using congrArg (fun bs : List Bool => bs.all id) he
  | or cs hcs ih =>
    have he : cs.map (fun c => (relabel f c).eval x) = cs.map (fun c => c.eval (x ∘ f)) := by
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [relabel,Circ.eval,List.any_map,any_dedup,Function.comp_def]
    simpa only [List.any_map,Function.comp_def] using congrArg (fun bs : List Bool => bs.any id) he

theorem depth_relabel {V W : Type} (f : V → W) (C : Circ V) : (relabel f C).depth ≤ C.depth := by
  classical
  cases C with
  | const b => simp only [relabel,Circ.depth,le_refl]
  | lit v b => simp only [relabel,Circ.depth,le_refl]
  | and cs =>
    have hm := map_max_mono cs (fun c => (relabel f c).depth) Circ.depth (fun c hc => depth_relabel f c)
    have hd := dedup_max_le (cs.map (relabel f)) Circ.depth
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [relabel,Circ.depth] using Nat.add_le_add_left (hd.trans hm) 1
  | or cs =>
    have hm := map_max_mono cs (fun c => (relabel f c).depth) Circ.depth (fun c hc => depth_relabel f c)
    have hd := dedup_max_le (cs.map (relabel f)) Circ.depth
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [relabel,Circ.depth] using Nat.add_le_add_left (hd.trans hm) 1
  | xor cs =>
    have hm := map_max_mono cs (fun c => (relabel f c).depth) Circ.depth (fun c hc => depth_relabel f c)
    simpa only [relabel,Circ.depth,List.map_map,Function.comp_def] using Nat.add_le_add_left hm 1
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem size_relabel {V W : Type} (f : V → W) (C : Circ V) : (relabel f C).treeSize ≤ C.treeSize := by
  classical
  cases C with
  | const b => simp only [relabel,Circ.treeSize,le_refl]
  | lit v b => simp only [relabel,Circ.treeSize,le_refl]
  | and cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (relabel f c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_relabel f c)
    have hd := dedup_sum_le (cs.map (relabel f)) Circ.treeSize
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [relabel,Circ.treeSize] using Nat.add_le_add_left (hd.trans hm) 1
  | or cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (relabel f c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_relabel f c)
    have hd := dedup_sum_le (cs.map (relabel f)) Circ.treeSize
    simp only [List.map_map,Function.comp_def] at hd
    simpa only [relabel,Circ.treeSize] using Nat.add_le_add_left (hd.trans hm) 1
  | xor cs =>
    have hm := List.sum_le_sum (l := cs) (f := fun c => (relabel f c).treeSize) (g := Circ.treeSize)
      (fun c hc => size_relabel f c)
    simpa only [relabel,Circ.treeSize,List.map_map,Function.comp_def] using Nat.add_le_add_left hm 1
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

end SemAC02.MonotoneCircuitRelabeling
end

section
-- Inlined Solutions.RelabeledOrFamily

set_option maxHeartbeats 1000000

open SemAC02.MonotoneCircuitRelabeling SemAC02.MonotoneCircuitPinning

namespace SemAC02.RelabeledOrFamily

noncomputable def children {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) : List (Circ (Fin m)) :=
  List.ofFn (fun i => relabel (σ i) C)

open Classical in
noncomputable def cover {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) : Circ (Fin m) :=
  .or (children C σ).dedup

theorem monotone_cover {m r s : ℕ} {C : Circ (Fin r)} (hC : IsMonotoneCirc C)
    (σ : Fin s → Fin r → Fin m) : IsMonotoneCirc (cover C σ) := by
  classical
  apply IsMonotoneCirc.or
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact monotone_relabel _ hC

theorem reduced_cover {m r s : ℕ} {C : Circ (Fin r)} (hC : IsMonotoneCirc C)
    (hR : IsReduced C) (hroot : C.isAnd = true) (σ : Fin s → Fin r → Fin m) : IsReduced (cover C σ) := by
  classical
  have hnot : C.isOr = false := by cases C <;> simp_all [Circ.isAnd,Circ.isOr]
  apply IsReduced.or
  · exact List.nodup_dedup _
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    simpa only [isOr_relabel] using hnot
  · intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
    exact reduced_relabel _ hC hR

theorem depth_cover {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) :
    (cover C σ).depth ≤ 1+C.depth := by
  classical
  simp only [cover,Circ.depth]
  apply Nat.add_le_add_left
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hk
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact depth_relabel _ C

theorem children_size {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) :
    ((children C σ).map Circ.treeSize).sum ≤ s*C.treeSize := by
  calc
    _ ≤ ((children C σ).map (fun _ => C.treeSize)).sum := by
      apply List.sum_le_sum
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact size_relabel _ C
    _ = _ := by simp [children,List.map_ofFn,Function.comp_def]

theorem size_cover {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) :
    (cover C σ).treeSize ≤ 1+s*C.treeSize := by
  classical
  have hs := (dedup_sum_le (children C σ) Circ.treeSize).trans (children_size C σ)
  simpa only [cover,Circ.treeSize] using Nat.add_le_add_left hs 1

theorem rooted_children {m r s d : ℕ} {C : Circ (Fin r)} (hroot : C.isAnd = true) (hd : C.depth ≤ d)
    (σ : Fin s → Fin r → Fin m) :
    ∃ cs, cover C σ = Circ.or cs ∧ ∀ c ∈ cs, c.isAnd = true ∧ c.depth ≤ d := by
  classical
  refine ⟨(children C σ).dedup,rfl,?_⟩
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_dedup.mp hc)
  exact ⟨by simpa only [isAnd_relabel] using hroot,(depth_relabel _ C).trans hd⟩

theorem eval_cover {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) (x : Fin m → Bool) :
    (cover C σ).eval x = !(decide (∀ i : Fin s, (relabel (σ i) C).eval x = false)) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [cover,Circ.eval,List.any_map,any_dedup,children]

end SemAC02.RelabeledOrFamily
end

section
-- Inlined Solutions.UniformRelabeling

set_option maxHeartbeats 1000000

open Finset SemAC02.BernoulliAlgebra ProofComplexity.FiniteProductPushforward

namespace SemAC02.UniformRelabeling

noncomputable def uniformWeight {A : Type*} [Fintype A] (_ : A) : ℝ := (Fintype.card A : ℝ)⁻¹

theorem uniformWeight_nonneg {A : Type*} [Fintype A] (a : A) : 0 ≤ uniformWeight a := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem uniformWeight_sum (A : Type*) [Fintype A] [Nonempty A] : ∑ a : A, uniformWeight a = 1 := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [uniformWeight,hc]

noncomputable def productWeight {I A : Type*} [Fintype I] [Fintype A] (σ : I → A) : ℝ :=
  ∏ i, uniformWeight (σ i)

theorem productWeight_nonneg {I A : Type*} [Fintype I] [Fintype A] (σ : I → A) :
    0 ≤ productWeight σ := prod_nonneg (fun _ _ => uniformWeight_nonneg _)

theorem productWeight_sum (I A : Type*) [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] :
    ∑ σ : I → A, productWeight σ = 1 := by
  simp only [productWeight]
  rw [← Fintype.prod_sum]
  simp only [uniformWeight_sum,prod_const_one]

noncomputable def density {m : ℕ} (x : Fin m → Bool) : ℝ := (hammingWeight x : ℝ)/(m : ℝ)

theorem bool_fiber {m : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool) (b : Bool) :
    (∑ j : Fin m, if x j = b then uniformWeight j else 0) = bitWeight (density x) b := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  have ht : (∑ j : Fin m, if x j = true then uniformWeight j else 0) = density x := by
    have hcount : (∑ j : Fin m, if x j = true then (1 : ℝ) else 0) = (hammingWeight x : ℝ) := by
      simp [hammingWeight]
    calc
      _ = (∑ j : Fin m, if x j = true then (1 : ℝ) else 0)*(m : ℝ)⁻¹ := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j _
        simp only [uniformWeight,Fintype.card_fin,ite_mul,one_mul,zero_mul]
      _ = _ := by rw [hcount]; simp only [density,div_eq_mul_inv]
  have hsum : (∑ j : Fin m, if x j = false then uniformWeight j else 0)+
      (∑ j : Fin m, if x j = true then uniformWeight j else 0) = 1 := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ j : Fin m, uniformWeight j := by
        apply sum_congr rfl
        intro j _
        cases he : x j <;> simp [he]
      _ = 1 := uniformWeight_sum _
  cases b
  · simp only [bitWeight,Bool.false_eq_true,↓reduceIte]
    linarith
  · simpa only [bitWeight,↓reduceIte] using ht

/-- Independent uniform labels turn a fixed Boolean input into independent bits of its density. -/
theorem average_labels {m r : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool)
    (E : (Fin r → Bool) → Bool) :
    (∑ σ : Fin r → Fin m, productWeight σ*(if E (x ∘ σ) then 1 else 0)) =
      bernProb (density x) E := by
  have h := sum_pushforward x (fun _ : Fin r => fun j : Fin m => uniformWeight j)
    (fun y : Fin r → Bool => if E y then 1 else 0)
  simp_rw [bool_fiber hm x] at h
  simpa only [productWeight,Function.comp_def,prob_eq_indicator,weight] using h

end SemAC02.UniformRelabeling
end

section
-- Inlined Solutions.MonotoneBernoulli

set_option maxHeartbeats 1000000

open Finset SemAC02.BernoulliAlgebra

namespace SemAC02.MonotoneBernoulli

theorem eval_mono {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) {x y : V → Bool}
    (hxy : ∀ v, x v = true → y v = true) : C.eval x = true → C.eval y = true := by
  induction hC with
  | const b => simpa only [Circ.eval] using (id : b = true → b = true)
  | lit v => simpa only [Circ.eval,↓reduceIte] using hxy v
  | and cs hcs ih =>
    simp only [Circ.eval,List.all_map,List.all_eq_true]
    intro h c hc
    exact ih c hc (h c hc)
  | or cs hcs ih =>
    simp only [Circ.eval,List.any_map,List.any_eq_true]
    rintro ⟨c,hc,he⟩
    exact ⟨c,hc,ih c hc he⟩

theorem prob_event_mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ}
    (E F : (Fin m → Bool) → Bool) (hEF : ∀ x, E x = true → F x = true) :
    bernProb p E ≤ bernProb p F := by
  rw [bernProb_eq_weight,bernProb_eq_weight]
  apply sum_le_sum
  intro x _
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    split_ifs
    · exact weight_nonneg hp hp' x
    · exact le_rfl
  · simp only [he,hEF x he,↓reduceIte,le_refl]

theorem prob_bias_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) {m : ℕ}
    (E : (Fin m → Bool) → Bool)
    (hE : ∀ x y : Fin m → Bool, (∀ i, x i = true → y i = true) → E x = true → E y = true) :
    bernProb p E ≤ bernProb q E := by
  classical
  have hp' : p ≤ 1 := hpq.trans hq
  by_cases hone : p = 1
  · have heq : p = q := by linarith
    rw [heq]
  have hplt : p < 1 := lt_of_le_of_ne hp' hone
  have hden : 0 < 1-p := by linarith
  let r := (q-p)/(1-p)
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hpq) hden.le
  have hr' : r ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have hbias : r+(1-r)*p = q := by
    dsimp [r]
    field_simp [hden.ne'] <;> ring
  have hpin (z : Fin m → Bool) : bernProb p E ≤ bernProb p (fun x => E (unionInputs z x)) := by
    apply prob_event_mono hp hp'
    intro x hx
    exact hE x (unionInputs z x) (by intro i hi; simp [unionInputs,hi]) hx
  calc
    bernProb p E = ∑ z : Fin m → Bool, weight r z * bernProb p E := by
      rw [← sum_mul,weight_sum,one_mul]
    _ ≤ ∑ z : Fin m → Bool, weight r z * bernProb p (fun x => E (unionInputs z x)) := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hpin z) (weight_nonneg hr hr' z)
    _ = bernProb (r+(1-r)*p) E := pinning_average r p E
    _ = bernProb q E := by rw [hbias]

theorem circuit_bias_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) {m : ℕ}
    {C : Circ (Fin m)} (hC : IsMonotoneCirc C) :
    bernProb p (fun x => C.eval x) ≤ bernProb q (fun x => C.eval x) :=
  prob_bias_mono hp hpq hq _ (fun _ _ hxy => eval_mono hC hxy)

end SemAC02.MonotoneBernoulli
end

section
-- Inlined Solutions.FiniteExpectation

set_option maxHeartbeats 1000000

open Finset

namespace ProofComplexity.FiniteExpectation

noncomputable def expect {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, w x*f x

noncomputable def prob {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Bool) : ℝ :=
  expect w (fun x => if E x then 1 else 0)

theorem expect_mono {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : expect w f ≤ expect w g :=
  sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x))

theorem expect_const {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∑ x, w x = 1) (a : ℝ) :
    expect w (fun _ => a) = a := by
  rw [expect,← sum_mul,hw,one_mul]

theorem expect_add {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    expect w (fun x => f x+g x) = expect w f+expect w g := by
  simp only [expect,mul_add,sum_add_distrib]

theorem expect_div {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (a : ℝ) :
    expect w (fun x => f x/a) = expect w f/a := by
  simp only [expect,mul_div_assoc,sum_div]

theorem prob_complement {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∑ x, w x = 1) (E : Ω → Bool) :
    prob w (fun x => !E x) = 1-prob w E := by
  have h : prob w E+prob w (fun x => !E x) = 1 := by
    rw [prob,prob,← expect_add]
    calc
      _ = expect w (fun _ => 1) := by
        congr 1
        funext x
        cases E x <;> norm_num
      _ = 1 := expect_const hw 1
  linarith

theorem exists_lt_expect_bound {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (f : Ω → ℝ) {a : ℝ} (hf : expect w f < a) : ∃ x, f x < a := by
  classical
  by_contra! hn
  have h := expect_mono hw hn
  rw [expect_const hw1 a] at h
  linarith

/-- A coverage failure probability and a mean acceptance bound can be met simultaneously. -/
theorem exists_good_small {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (bad : Ω → Bool) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 < a) (hbad : prob w bad < 1/2) (hmean : expect w f < a/2) :
    ∃ x, bad x = false ∧ f x ≤ a := by
  have hdiv : expect w f/a < 1/2 := (div_lt_iff₀ ha).mpr (by linarith)
  have hcost : expect w (fun x => (if bad x then 1 else 0)+f x/a) < 1 := by
    rw [expect_add,expect_div]
    change prob w bad+expect w f/a < 1
    linarith
  obtain ⟨x,hx⟩ := exists_lt_expect_bound hw hw1 _ hcost
  have hfalse : bad x = false := by
    cases he : bad x
    · rfl
    · have hd : 0 ≤ f x/a := div_nonneg (hf x) ha.le
      simp only [he,↓reduceIte] at hx
      linarith
  refine ⟨x,hfalse,?_⟩
  simp only [hfalse,Bool.false_eq_true,↓reduceIte,zero_add] at hx
  exact ((div_lt_one ha).mp hx).le

end ProofComplexity.FiniteExpectation
end

section
-- Inlined Solutions.RandomRelabeledCircuit

set_option maxHeartbeats 1000000

open SemAC02.UniformRelabeling SemAC02.MonotoneCircuitRelabeling

namespace SemAC02.RandomRelabeledCircuit

theorem density_nonneg {m : ℕ} (x : Fin m → Bool) : 0 ≤ density x :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem weight_le_dimension {m : ℕ} (x : Fin m → Bool) : hammingWeight x ≤ m := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i : Fin m => x i = true) Finset.univ)
  simpa only [hammingWeight,Finset.card_univ,Fintype.card_fin] using h

theorem density_le_one {m : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool) : density x ≤ 1 := by
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m from by omega)
  apply (div_le_iff₀ hpos).mpr
  simpa only [one_mul] using (show (hammingWeight x : ℝ) ≤ (m : ℝ) from by exact_mod_cast weight_le_dimension x)

theorem acceptance_average {m r : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool)
    {C : Circ (Fin r)} (hC : IsMonotoneCirc C) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin r → Fin m => productWeight σ)
      (fun σ => (relabel σ C).eval x) = bernProb (density x) (fun y => C.eval y) := by
  simp only [ProofComplexity.FiniteExpectation.prob,ProofComplexity.FiniteExpectation.expect,eval_relabel _ hC]
  exact average_labels hm x (fun y => C.eval y)

theorem high_density_acceptance {m r : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool)
    (hx : (m : ℝ)/2 ≤ (hammingWeight x : ℝ)) {C : Circ (Fin r)} (hC : IsMonotoneCirc C) :
    bernProb (1/2) (fun y => C.eval y) ≤
      ProofComplexity.FiniteExpectation.prob (fun σ : Fin r → Fin m => productWeight σ)
        (fun σ => (relabel σ C).eval x) := by
  rw [acceptance_average hm x hC]
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m from by omega)
  apply MonotoneBernoulli.circuit_bias_mono (by norm_num) _ (density_le_one hm x) hC
  apply (le_div_iff₀ hpos).mpr
  linarith

theorem low_density_acceptance {m r : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool) (p : ℝ)
    (hp : p ≤ 1) (hx : (hammingWeight x : ℝ) ≤ p*(m : ℝ))
    {C : Circ (Fin r)} (hC : IsMonotoneCirc C) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin r → Fin m => productWeight σ)
      (fun σ => (relabel σ C).eval x) ≤ bernProb p (fun y => C.eval y) := by
  rw [acceptance_average hm x hC]
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m from by omega)
  exact MonotoneBernoulli.circuit_bias_mono (density_nonneg x) ((div_le_iff₀ hpos).mpr hx) hp hC

end SemAC02.RandomRelabeledCircuit
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
-- Inlined Solutions.ProductExpectation

set_option maxHeartbeats 1000000

open Finset ProofComplexity.FiniteExpectation

namespace ProofComplexity.ProductExpectation

noncomputable def productLaw {I A : Type*} [Fintype I] (w : A → ℝ) (x : I → A) : ℝ := ∏ i, w (x i)

theorem productLaw_nonneg {I A : Type*} [Fintype I] {w : A → ℝ} (hw : ∀ a, 0 ≤ w a) (x : I → A) :
    0 ≤ productLaw w x := prod_nonneg (fun i _ => hw (x i))

theorem productLaw_sum {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    {w : A → ℝ} (hw : ∑ a, w a = 1) : ∑ x : I → A, productLaw w x = 1 := by
  simp only [productLaw]
  rw [← Fintype.prod_sum]
  simp only [hw,prod_const_one]

theorem prob_all {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (w : A → ℝ) (E : A → Bool) :
    prob (fun x : I → A => productLaw w x) (fun x => decide (∀ i, E (x i) = true)) =
      prob w E ^ Fintype.card I := by
  classical
  simp only [prob,FiniteExpectation.expect,productLaw,mul_ite,mul_one,mul_zero]
  simp_rw [SemAC02.BernoulliProduct.indicator_all]
  rw [← Fintype.prod_sum (fun _ : I => fun a : A => if E a then w a else 0)]
  simp only [prod_const,card_univ]

theorem prob_all_reject {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    {w : A → ℝ} (hw : ∑ a, w a = 1) (E : A → Bool) :
    prob (fun x : I → A => productLaw w x) (fun x => decide (∀ i, E (x i) = false)) =
      (1-prob w E)^Fintype.card I := by
  have h := prob_all (I := I) w (fun a => !E a)
  rw [prob_complement hw] at h
  convert h using 1
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp

theorem prob_any {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    {w : A → ℝ} (hw : ∑ a, w a = 1) (E : A → Bool) :
    prob (fun x : I → A => productLaw w x) (fun x => !(decide (∀ i, E (x i) = false))) =
      1-(1-prob w E)^Fintype.card I := by
  rw [prob_complement (productLaw_sum hw),prob_all_reject hw]

end ProofComplexity.ProductExpectation
end

section
-- Inlined Solutions.FiniteUnionBound

set_option maxHeartbeats 1000000

open Finset

namespace ProofComplexity.FiniteExpectation

theorem prob_nonneg {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (E : Ω → Bool) :
    0 ≤ prob w E := by
  apply sum_nonneg
  intro x _
  apply mul_nonneg (hw x)
  change 0 ≤ (if E x then (1 : ℝ) else 0)
  split_ifs <;> norm_num

theorem prob_le_one {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (E : Ω → Bool) : prob w E ≤ 1 := by
  calc
    _ ≤ expect w (fun _ => 1) := expect_mono hw (by intro x; split_ifs <;> norm_num)
    _ = _ := expect_const hw1 1

theorem prob_event_mono {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (E F : Ω → Bool) (hEF : ∀ x, E x = true → F x = true) : prob w E ≤ prob w F := by
  apply expect_mono hw
  intro x
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    split_ifs <;> norm_num
  · simp only [he,hEF x he,↓reduceIte,le_refl]

theorem prob_exists_le_sum {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (E : I → Ω → Bool) :
    prob w (fun x => decide (∃ i, E i x = true)) ≤ ∑ i, prob w (E i) := by
  classical
  have hind (x : Ω) : (if decide (∃ i, E i x = true) then (1 : ℝ) else 0) ≤
      ∑ i, if E i x then 1 else 0 := by
    by_cases he : ∃ i, E i x = true
    · obtain ⟨i,hi⟩ := he
      simp only [show (∃ i, E i x = true) from ⟨i,hi⟩,decide_true,↓reduceIte]
      calc
        (1 : ℝ) = if E i x then 1 else 0 := by simp only [hi,↓reduceIte]
        _ ≤ _ := single_le_sum (f := fun j : I => if E j x then (1 : ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    · simp only [he,decide_false,Bool.false_eq_true,↓reduceIte]
      apply sum_nonneg
      intro i _
      split_ifs <;> norm_num
  calc
    _ ≤ expect w (fun x => ∑ i, if E i x then 1 else 0) := expect_mono hw hind
    _ = _ := by simp only [expect,prob,mul_sum]; rw [sum_comm]

end ProofComplexity.FiniteExpectation
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
-- Inlined Solutions.RandomOrFamily

set_option maxHeartbeats 1000000

open SemAC02.UniformRelabeling SemAC02.MonotoneCircuitRelabeling SemAC02.RelabeledOrFamily
open ProofComplexity.ProductExpectation

namespace SemAC02.RandomOrFamily

noncomputable def familyLaw {m r s : ℕ} (σ : Fin s → Fin r → Fin m) : ℝ :=
  productLaw (fun f : Fin r → Fin m => productWeight f) σ

theorem familyLaw_nonneg {m r s : ℕ} (σ : Fin s → Fin r → Fin m) : 0 ≤ familyLaw σ :=
  productLaw_nonneg productWeight_nonneg σ

theorem familyLaw_sum {m r s : ℕ} (hm : 1 ≤ m) : ∑ σ : Fin s → Fin r → Fin m, familyLaw σ = 1 := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  exact productLaw_sum (productWeight_sum (Fin r) (Fin m))

theorem acceptance_exact {m r s : ℕ} (hm : 1 ≤ m) (C : Circ (Fin r)) (x : Fin m → Bool) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => (cover C σ).eval x) =
      1-(1-ProofComplexity.FiniteExpectation.prob (fun f : Fin r → Fin m => productWeight f)
        (fun f => (relabel f C).eval x))^s := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  have h := prob_any (I := Fin s) (productWeight_sum (Fin r) (Fin m))
    (fun f : Fin r → Fin m => (relabel f C).eval x)
  convert h using 1
  · simp only [familyLaw,eval_cover]
    congr 1
    funext σ
    apply Bool.eq_iff_iff.mpr
    simp
  · simp only [Fintype.card_fin]

theorem rejection_exact {m r s : ℕ} (hm : 1 ≤ m) (C : Circ (Fin r)) (x : Fin m → Bool) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => !(cover C σ).eval x) =
      (1-ProofComplexity.FiniteExpectation.prob (fun f : Fin r → Fin m => productWeight f)
        (fun f => (relabel f C).eval x))^s := by
  rw [ProofComplexity.FiniteExpectation.prob_complement (familyLaw_sum hm),acceptance_exact hm C x]
  ring

theorem acceptance_le_mul {m r s : ℕ} (hm : 1 ≤ m) (C : Circ (Fin r)) (x : Fin m → Bool)
    (β : ℝ) (hβ : ProofComplexity.FiniteExpectation.prob (fun f : Fin r → Fin m => productWeight f)
      (fun f => (relabel f C).eval x) ≤ β) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => (cover C σ).eval x) ≤ (s : ℝ)*β := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  rw [acceptance_exact hm C x]
  apply (CoinDepthTwoNumerics.union_power_bound
    (ProofComplexity.FiniteExpectation.prob_nonneg productWeight_nonneg _)
    (ProofComplexity.FiniteExpectation.prob_le_one productWeight_nonneg (productWeight_sum (Fin r) (Fin m)) _) s).trans
  exact mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg s)

theorem rejection_le_exp {m r s : ℕ} (hm : 1 ≤ m) (C : Circ (Fin r)) (x : Fin m → Bool)
    (α : ℝ) (hα : α ≤ ProofComplexity.FiniteExpectation.prob (fun f : Fin r → Fin m => productWeight f)
      (fun f => (relabel f C).eval x)) (hs : 4*(m : ℝ) ≤ (s : ℝ)*α) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => !(cover C σ).eval x) ≤ Real.exp (-4*(m : ℝ)) := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  rw [rejection_exact hm C x]
  apply (CoinDepthTwoNumerics.failure_power_bound
    (ProofComplexity.FiniteExpectation.prob_le_one productWeight_nonneg (productWeight_sum (Fin r) (Fin m)) _) s).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg s)
  nlinarith

end SemAC02.RandomOrFamily
end

section
-- Inlined Solutions.CoveringFailureNumerics

set_option maxHeartbeats 1000000

namespace SemAC02.CoveringFailureNumerics

theorem cube_failure_lt_half (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ)^m*Real.exp (-4*(m : ℝ)) < 1/2 := by
  have hb : 2*Real.exp (-4) ≤ 2/5 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 4)).mpr
    linarith [Real.add_one_le_exp 4]
  calc
    _ = (2*Real.exp (-4))^m := by
      rw [mul_pow,← Real.exp_nat_mul]
      congr 1
      congr 1
      ring
    _ ≤ (2/5 : ℝ)^m := pow_le_pow_left₀ (by positivity) hb m
    _ ≤ 2/5 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    _ < _ := by norm_num

end SemAC02.CoveringFailureNumerics
end

section
-- Inlined Solutions.CoveringFailureBounds

set_option maxHeartbeats 1000000

open SemAC02.RelabeledOrFamily SemAC02.RandomOrFamily SemAC02.UniformRelabeling
open SemAC02.MonotoneCircuitRelabeling

namespace SemAC02.CoveringFailureBounds

noncomputable def badCoverage {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m) : Bool :=
  decide (∃ x : Fin m → Bool, (m : ℝ)/2 ≤ (hammingWeight x : ℝ) ∧ (cover C σ).eval x = false)

theorem coverage_of_not_bad {m r s : ℕ} (C : Circ (Fin r)) (σ : Fin s → Fin r → Fin m)
    (hb : badCoverage C σ = false) (x : Fin m → Bool) (hx : (m : ℝ)/2 ≤ (hammingWeight x : ℝ)) :
    (cover C σ).eval x = true := by
  have hn : ¬∃ y : Fin m → Bool, (m : ℝ)/2 ≤ (hammingWeight y : ℝ) ∧ (cover C σ).eval y = false :=
    of_decide_eq_false hb
  cases he : (cover C σ).eval x
  · exact (hn ⟨x,hx,he⟩).elim
  · rfl

theorem failure_probability_bound {m r s : ℕ} (hm : 1 ≤ m) {C : Circ (Fin r)}
    (hC : IsMonotoneCirc C) (α : ℝ) (hα : α ≤ bernProb (1/2) (fun y => C.eval y))
    (hs : 4*(m : ℝ) ≤ (s : ℝ)*α) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => badCoverage C σ) ≤ (2 : ℝ)^m*Real.exp (-4*(m : ℝ)) := by
  classical
  let E := fun (x : Fin m → Bool) (σ : Fin s → Fin r → Fin m) =>
    decide ((m : ℝ)/2 ≤ (hammingWeight x : ℝ) ∧ (cover C σ).eval x = false)
  have hu : ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => badCoverage C σ) ≤
      ∑ x : Fin m → Bool, ProofComplexity.FiniteExpectation.prob
        (fun σ : Fin s → Fin r → Fin m => familyLaw σ) (E x) := by
    convert ProofComplexity.FiniteExpectation.prob_exists_le_sum familyLaw_nonneg E using 1
    congr 1
    funext σ
    apply Bool.eq_iff_iff.mpr
    simp only [badCoverage,E,decide_eq_true_eq]
  have hxbound (x : Fin m → Bool) : ProofComplexity.FiniteExpectation.prob
      (fun σ : Fin s → Fin r → Fin m => familyLaw σ) (E x) ≤ Real.exp (-4*(m : ℝ)) := by
    by_cases hx : (m : ℝ)/2 ≤ (hammingWeight x : ℝ)
    · have ha := hα.trans (RandomRelabeledCircuit.high_density_acceptance hm x hx hC)
      apply (ProofComplexity.FiniteExpectation.prob_event_mono familyLaw_nonneg (E x)
        (fun σ => !(cover C σ).eval x) ?_).trans (rejection_le_exp hm C x α ha hs)
      intro σ he
      have h : (m : ℝ)/2 ≤ (hammingWeight x : ℝ) ∧ (cover C σ).eval x = false := of_decide_eq_true he
      rw [h.2]
      rfl
    · have he : E x = (fun _ : Fin s → Fin r → Fin m => false) := by
        funext σ
        simp only [E,hx,false_and,decide_false]
      rw [he]
      simp only [ProofComplexity.FiniteExpectation.prob,ProofComplexity.FiniteExpectation.expect,
        Bool.false_eq_true,↓reduceIte,mul_zero,Finset.sum_const_zero]
      exact (Real.exp_pos _).le
  calc
    _ ≤ ∑ x : Fin m → Bool, ProofComplexity.FiniteExpectation.prob
        (fun σ : Fin s → Fin r → Fin m => familyLaw σ) (E x) := hu
    _ ≤ ∑ _ : Fin m → Bool, Real.exp (-4*(m : ℝ)) := Finset.sum_le_sum (fun x _ => hxbound x)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
        Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

theorem failure_probability_lt_half {m r s : ℕ} (hm : 1 ≤ m) {C : Circ (Fin r)}
    (hC : IsMonotoneCirc C) (α : ℝ) (hα : α ≤ bernProb (1/2) (fun y => C.eval y))
    (hs : 4*(m : ℝ) ≤ (s : ℝ)*α) :
    ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => badCoverage C σ) < 1/2 :=
  (failure_probability_bound hm hC α hα hs).trans_lt (CoveringFailureNumerics.cube_failure_lt_half m hm)

end SemAC02.CoveringFailureBounds
end

section
-- Inlined Solutions.CoveringMean

set_option maxHeartbeats 1000000

open Finset

namespace ProofComplexity.FiniteExpectation

theorem expect_prob_swap {Ω X : Type*} [Fintype Ω] [Fintype X] (w : Ω → ℝ) (v : X → ℝ)
    (E : Ω → X → Bool) :
    expect w (fun a => prob v (E a)) = expect v (fun x => prob w (fun a => E a x)) := by
  simp only [prob,expect,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro a _
  ring

/-- Bound the average acceptance by splitting the input distribution at a weight threshold. -/
theorem split_mean_bound {Ω X : Type*} [Fintype Ω] [Fintype X] {w : Ω → ℝ} {v : X → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (hv : ∀ x, 0 ≤ v x) (hv1 : ∑ x, v x = 1)
    (E : Ω → X → Bool) (bad : X → Bool) {β : ℝ} (hβ : 0 ≤ β)
    (hgood : ∀ x, bad x = false → prob w (fun a => E a x) ≤ β) :
    expect w (fun a => prob v (E a)) ≤ β+prob v bad := by
  rw [expect_prob_swap]
  calc
    _ ≤ expect v (fun x => β+(if bad x then 1 else 0)) := by
      apply expect_mono hv
      intro x
      cases he : bad x
      · simpa only [he,Bool.false_eq_true,↓reduceIte,add_zero] using hgood x he
      · have h := prob_le_one hw hw1 (fun a => E a x)
        simp only [he,↓reduceIte]
        linarith
    _ = _ := by rw [expect_add,expect_const hv1 β]; rfl

end ProofComplexity.FiniteExpectation
end

section
-- Inlined Solutions.BernoulliTail

set_option maxHeartbeats 2000000

open Finset SemAC02.BernoulliAlgebra

namespace SemAC02.BernoulliTail

def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem weight_eq_sum {m : ℕ} (x : Fin m → Bool) :
    (hammingWeight x : ℝ) = ∑ i, bitValue (x i) := by
  simp [hammingWeight,bitValue]

theorem exp_weight {m : ℕ} (θ : ℝ) (x : Fin m → Bool) :
    Real.exp (θ*(hammingWeight x : ℝ)) = ∏ i, Real.exp (θ*bitValue (x i)) := by
  rw [weight_eq_sum,mul_sum,Real.exp_sum]

theorem moment_formula {m : ℕ} (p θ : ℝ) :
    (∑ x : Fin m → Bool, weight p x*Real.exp (θ*(hammingWeight x : ℝ))) =
      (1-p+p*Real.exp θ)^m := by
  simp_rw [exp_weight,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : Fin m => fun b : Bool => bitWeight p b*Real.exp (θ*bitValue b))]
  simp [bitWeight,bitValue,add_comm]

theorem moment_markov {m : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (t : ℝ) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → t ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-θ*t)*(1-p+p*Real.exp θ)^m := by
  have hs : bernProb p E*Real.exp (θ*t) ≤ (1-p+p*Real.exp θ)^m := by
    rw [bernProb_eq_weight,sum_mul,← moment_formula]
    apply sum_le_sum
    intro x _
    cases he : E x
    · simp only [he,Bool.false_eq_true,↓reduceIte,zero_mul]
      exact mul_nonneg (weight_nonneg hp hp' x) (Real.exp_pos _).le
    · simp only [he,↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hE x he) hθ)) (weight_nonneg hp hp' x)
  calc
    _ = (bernProb p E*Real.exp (θ*t))*Real.exp (-θ*t) := by
      rw [mul_assoc,← Real.exp_add,show θ*t+(-θ*t) = 0 by ring,Real.exp_zero,mul_one]
    _ ≤ (1-p+p*Real.exp θ)^m*Real.exp (-θ*t) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem exp_quadratic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    Real.exp θ ≤ 1+θ+2*θ^2 := by
  apply (Real.exp_bound_div_one_sub_of_interval hθ (by linarith : θ < 1)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-θ)).mpr
  nlinarith [mul_nonneg (sq_nonneg θ) (by linarith : 0 ≤ 1-2*θ)]

theorem moment_bound {m : ℕ} {p θ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    (1-p+p*Real.exp θ)^m ≤ Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) := by
  have hb : 1-p+p*Real.exp θ ≤ Real.exp (p*θ+2*p*θ^2) := by
    have he := mul_le_mul_of_nonneg_left (exp_quadratic_bound hθ hθ') hp
    linarith [Real.add_one_le_exp (p*θ+2*p*θ^2)]
  calc
    _ ≤ Real.exp (p*θ+2*p*θ^2)^m := pow_le_pow_left₀
      (add_nonneg (sub_nonneg.mpr hp') (mul_nonneg hp (Real.exp_pos _).le)) hb m
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- A finite-sum Chernoff estimate; its constant suffices for the covering-gadget construction. -/
theorem upper_tail {m : ℕ} {p δ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → (p+δ)*(m : ℝ) ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-((m : ℝ)*δ^2/4)) := by
  let θ := δ/2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ' : θ ≤ 1/2 := by dsimp [θ]; linarith
  calc
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*(1-p+p*Real.exp θ)^m :=
      moment_markov hp (by linarith : p ≤ 1) hθ _ E hE
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) :=
      mul_le_mul_of_nonneg_left (moment_bound hp (by linarith : p ≤ 1) hθ hθ') (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ)*(2*p*θ^2-θ*δ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hsmall : 2*p*θ^2-θ*δ ≤ -δ^2/4 := by
        dsimp [θ]
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*p) (sq_nonneg δ)]
      have h := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg m)
      nlinarith

theorem covering_tail {m : ℕ} {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/2) :
    bernProb (1/2-ε)
      (fun x : Fin m → Bool => decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) ≤
      Real.exp (-((m : ℝ)*ε^2/64)) := by
  have h := upper_tail (p := 1/2-ε) (δ := ε/4) (by linarith) (by linarith)
    (by positivity) (by linarith) (fun x : Fin m → Bool =>
      decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) (by
        intro x hx
        have ht := of_decide_eq_true hx
        nlinarith)
  convert h using 1 <;> congr 1 <;> ring

end SemAC02.BernoulliTail
end

section
-- Inlined Solutions.CoveringAcceptanceBounds

set_option maxHeartbeats 1000000

open SemAC02.RelabeledOrFamily SemAC02.RandomOrFamily SemAC02.BernoulliAlgebra
open SemAC02.UniformRelabeling SemAC02.MonotoneCircuitRelabeling

namespace SemAC02.CoveringAcceptanceBounds

theorem prob_bernoulli {m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    ProofComplexity.FiniteExpectation.prob (fun x : Fin m → Bool => weight p x) E = bernProb p E := by
  simp only [ProofComplexity.FiniteExpectation.prob,ProofComplexity.FiniteExpectation.expect,
    mul_ite,mul_one,mul_zero,bernProb_eq_weight]

theorem split_acceptance {m r s : ℕ} (hm : 1 ≤ m) {C : Circ (Fin r)} (hC : IsMonotoneCirc C)
    {p δ β : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hshift : p+δ ≤ 1) (hβ : 0 ≤ β)
    (hCβ : bernProb (p+δ) (fun y => C.eval y) ≤ β) :
    ProofComplexity.FiniteExpectation.expect (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => bernProb p (fun x => (cover C σ).eval x)) ≤
      (s : ℝ)*β+bernProb p
        (fun x : Fin m → Bool => decide ((p+δ)*(m : ℝ) < (hammingWeight x : ℝ))) := by
  let bad := fun x : Fin m → Bool => decide ((p+δ)*(m : ℝ) < (hammingWeight x : ℝ))
  have hgood (x : Fin m → Bool) (hx : bad x = false) :
      ProofComplexity.FiniteExpectation.prob (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
        (fun σ => (cover C σ).eval x) ≤ (s : ℝ)*β := by
    have hwx : (hammingWeight x : ℝ) ≤ (p+δ)*(m : ℝ) := by
      have hn : ¬(p+δ)*(m : ℝ) < (hammingWeight x : ℝ) := of_decide_eq_false hx
      exact le_of_not_gt hn
    have ha := (RandomRelabeledCircuit.low_density_acceptance hm x (p+δ) hshift hwx hC).trans hCβ
    exact acceptance_le_mul hm C x β ha
  have h := ProofComplexity.FiniteExpectation.split_mean_bound familyLaw_nonneg (familyLaw_sum hm)
    (weight_nonneg hp hp') (weight_sum (Fin m) p) (fun σ x => (cover C σ).eval x) bad
    (show 0 ≤ (s : ℝ)*β from mul_nonneg (Nat.cast_nonneg s) hβ) hgood
  simpa only [prob_bernoulli] using h

theorem low_mean_bound {m r s : ℕ} (hm : 1 ≤ m) {C : Circ (Fin r)} (hC : IsMonotoneCirc C)
    {ε β : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/2) (hβ : 0 ≤ β)
    (hCβ : bernProb (1/2-3*ε/4) (fun y => C.eval y) ≤ β) :
    ProofComplexity.FiniteExpectation.expect (fun σ : Fin s → Fin r → Fin m => familyLaw σ)
      (fun σ => bernProb (1/2-ε) (fun x => (cover C σ).eval x)) ≤
      (s : ℝ)*β+Real.exp (-((m : ℝ)*ε^2/64)) := by
  have hs := split_acceptance (s := s) hm hC (p := 1/2-ε) (δ := ε/4)
    (by linarith) (by linarith) (by linarith) hβ (by
      convert hCβ using 1 <;> congr 1 <;> ring)
  have ht := BernoulliTail.covering_tail (m := m) hε hε'
  have hsame : (1/2-ε)+ε/4 = (1/2-3*ε/4 : ℝ) := by ring
  rw [hsame] at hs
  linarith

end SemAC02.CoveringAcceptanceBounds
end

section
-- Inlined Solutions.CoveringProbabilisticMethod

set_option maxHeartbeats 1000000

open SemAC02.RelabeledOrFamily SemAC02.RandomOrFamily SemAC02.CoveringFailureBounds

namespace SemAC02.CoveringProbabilisticMethod

/-- The finite probabilistic construction of the covering formula, with its numerical budgets
left as explicit inequalities for the final parameter calculation. -/
theorem exists_cover {m r s d : ℕ} (hm : 1 ≤ m) {C : Circ (Fin r)}
    (hC : IsMonotoneCirc C) (hR : IsReduced C) (hroot : C.isAnd = true) (hdepth : C.depth ≤ d)
    {ε α β L : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/2) (hβ : 0 ≤ β)
    (hfair : α ≤ bernProb (1/2) (fun y => C.eval y))
    (hlow : bernProb (1/2-3*ε/4) (fun y => C.eval y) ≤ β)
    (hs : 4*(m : ℝ) ≤ (s : ℝ)*α)
    (hbudget : (s : ℝ)*β+Real.exp (-((m : ℝ)*ε^2/64)) < Real.exp (-L)/2) :
    ∃ Cm : Circ (Fin m), IsMonotoneCirc Cm ∧ IsReduced Cm ∧ Cm.depth ≤ d+1 ∧
      Cm.treeSize ≤ 1+s*C.treeSize ∧
      (∃ cs, Cm = Circ.or cs ∧ ∀ c ∈ cs, c.isAnd = true ∧ c.depth ≤ d) ∧
      (∀ x : Fin m → Bool, (m : ℝ)/2 ≤ (hammingWeight x : ℝ) → Cm.eval x = true) ∧
      bernProb (1/2-ε) (fun x => Cm.eval x) ≤ Real.exp (-L) := by
  have hfail := failure_probability_lt_half (s := s) hm hC α hfair hs
  have hmean := CoveringAcceptanceBounds.low_mean_bound (s := s) hm hC hε hε' hβ hlow
  obtain ⟨σ,hnot,hacc⟩ := ProofComplexity.FiniteExpectation.exists_good_small
    (w := fun σ : Fin s → Fin r → Fin m => familyLaw σ) familyLaw_nonneg (familyLaw_sum hm)
    (fun σ => badCoverage C σ) (fun σ => bernProb (1/2-ε) (fun x => (cover C σ).eval x))
    (fun σ => BernoulliAlgebra.prob_nonneg (by linarith : 0 ≤ 1/2-ε) (by linarith : 1/2-ε ≤ 1) _)
    (Real.exp_pos (-L)) hfail (hmean.trans_lt hbudget)
  refine ⟨cover C σ,monotone_cover hC σ,reduced_cover hC hR hroot σ,?_,size_cover C σ,
    rooted_children hroot hdepth σ,?_,hacc⟩
  · exact (depth_cover C σ).trans (by omega)
  · intro x hx
    exact coverage_of_not_bad C σ hnot x hx

end SemAC02.CoveringProbabilisticMethod
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
-- Inlined Solutions.CoveringDimension

set_option maxHeartbeats 1000000

namespace SemAC02.CoveringDimension

theorem scale_power {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d) :
    (ε^(-1/((d : ℝ)-1)))^(d-1) = ε⁻¹ := by
  have hr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn : (d : ℝ)-1 ≠ 0 := by linarith
  rw [← Real.rpow_mul_natCast hε.le,Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
  rw [show (-1/((d : ℝ)-1))*((d : ℝ)-1) = -1 by field_simp]
  exact Real.rpow_neg_one ε

theorem scale_dimension_identity {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d) :
    (ε^(-1/((d : ℝ)-1)))^(2*d-1)*ε^2 = ε^(-1/((d : ℝ)-1)) := by
  rw [show 2*d-1 = (d-1)*2+1 by omega,pow_succ,pow_mul,scale_power hε hd]
  field_simp

theorem small_parameter_scale {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d)
    (hsmall : ε < 1/C^(d-1)) : C ≤ ε^(-1/((d : ℝ)-1)) := by
  have hcpos : 0 < C^(d-1) := pow_pos hC _
  have hprod : ε*C^(d-1) < 1 := (lt_div_iff₀ hcpos).mp hsmall
  have hp : C^(d-1) < (ε^(-1/((d : ℝ)-1)))^(d-1) := by
    rw [scale_power hε hd]
    have h := (lt_div_iff₀ hε).mpr (show C^(d-1)*ε < (1 : ℝ) from by nlinarith)
    simpa only [one_div] using h
  by_contra! hn
  have hle := pow_le_pow_left₀ (Real.rpow_nonneg hε.le _) hn.le (d-1)
  linarith

theorem smallest_odd_upper {x : ℝ} (hx : 3 ≤ x) {m : ℕ} (hm : Odd m) (hxm : x ≤ (m : ℝ))
    (hmin : ∀ m' : ℕ, Odd m' → x ≤ (m' : ℝ) → m ≤ m') : (m : ℝ) < x+2 := by
  have hm3 : 3 ≤ m := by exact_mod_cast (show (3 : ℝ) ≤ (m : ℝ) from hx.trans hxm)
  by_contra! hn
  have hodd : Odd (m-2) := Nat.Odd.sub_even (by omega) hm (by decide : Even 2)
  have hdown : x ≤ ((m-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m),Nat.cast_ofNat]
    linarith
  have h := hmin (m-2) hodd hdown
  omega

theorem dimension_bounds {L : ℝ} (hL : 1 ≤ L) (n : ℕ) {m : ℕ} (hm : Odd m)
    (hml : 128*L^n ≤ (m : ℝ))
    (hmin : ∀ m' : ℕ, Odd m' → 128*L^n ≤ (m' : ℝ) → m ≤ m') :
    1 ≤ m ∧ (m : ℝ) ≤ 130*L^n := by
  have hp : 1 ≤ L^n := one_le_pow₀ hL
  have hx : (3 : ℝ) ≤ 128*L^n := by nlinarith
  have hu := smallest_odd_upper hx hm hml hmin
  constructor
  · have h : (1 : ℝ) ≤ (m : ℝ) := by nlinarith
    exact_mod_cast h
  · nlinarith

theorem dimension_tail_exponent {ε : ℝ} (hε : 0 < ε) {d m : ℕ} (hd : 2 ≤ d)
    (hm : 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ)) :
    2*ε^(-1/((d : ℝ)-1)) ≤ (m : ℝ)*ε^2/64 := by
  have h := mul_le_mul_of_nonneg_right hm (sq_nonneg ε)
  rw [mul_assoc,scale_dimension_identity hε hd] at h
  nlinarith

end SemAC02.CoveringDimension
end

section
-- Inlined Solutions.CoveringSampleParameters

set_option maxHeartbeats 2000000

namespace SemAC02.CoveringSampleParameters

noncomputable def amplificationCount (L : ℝ) : ℕ := ⌈10*L⌉₊
noncomputable def copyCount (m t : ℕ) : ℕ := ⌈4*(m : ℝ)*(5/4 : ℝ)^t⌉₊
noncomputable def cutoff (n : ℕ) : ℝ := 521*(n.factorial : ℝ)+8

theorem cutoff_ge_eight (n : ℕ) : 8 ≤ cutoff n := by
  unfold cutoff
  have h : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  linarith

theorem amplification_bounds {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ amplificationCount L ∧ 10*L ≤ (amplificationCount L : ℝ) ∧
      (amplificationCount L : ℝ) ≤ 11*L := by
  have hlo := Nat.le_ceil (10*L)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 10*L from by positivity)
  refine ⟨Nat.one_le_ceil_iff.mpr (by positivity),hlo,?_⟩
  change (⌈10*L⌉₊ : ℝ) ≤ 11*L
  linarith

theorem copy_bounds (m t : ℕ) :
    4*(m : ℝ)*(5/4 : ℝ)^t ≤ (copyCount m t : ℝ) ∧
      (copyCount m t : ℝ) ≤ 4*(m : ℝ)*(5/4 : ℝ)^t+1 :=
  ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (by positivity)).le⟩

theorem coverage_mass (m t : ℕ) : 4*(m : ℝ) ≤ (copyCount m t : ℝ)*(4/5 : ℝ)^t := by
  have hc := mul_le_mul_of_nonneg_right (copy_bounds m t).1 (show 0 ≤ (4/5 : ℝ)^t from by positivity)
  have hcancel : (5/4 : ℝ)^t*(4/5 : ℝ)^t = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = (4*(m : ℝ)*(5/4 : ℝ)^t)*(4/5 : ℝ)^t := by rw [mul_assoc,hcancel,mul_one]
    _ ≤ _ := hc

theorem low_mass (m t : ℕ) :
    (copyCount m t : ℝ)*(1/5 : ℝ)^t ≤ (4*(m : ℝ)+1)*(1/4 : ℝ)^t := by
  have hc := mul_le_mul_of_nonneg_right (copy_bounds m t).2 (show 0 ≤ (1/5 : ℝ)^t from by positivity)
  have hprod : (5/4 : ℝ)^t*(1/5 : ℝ)^t = (1/4 : ℝ)^t := by rw [← mul_pow]; norm_num
  have hp : (1/5 : ℝ)^t ≤ (1/4 : ℝ)^t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  calc
    _ ≤ (4*(m : ℝ)*(5/4 : ℝ)^t+1)*(1/5 : ℝ)^t := hc
    _ = 4*(m : ℝ)*((5/4 : ℝ)^t*(1/5 : ℝ)^t)+(1/5 : ℝ)^t := by ring
    _ = 4*(m : ℝ)*(1/4 : ℝ)^t+(1/5 : ℝ)^t := by rw [hprod]
    _ ≤ 4*(m : ℝ)*(1/4 : ℝ)^t+(1/4 : ℝ)^t := by linarith
    _ = _ := by ring

theorem quarter_le_exp_neg_one : (1/4 : ℝ) ≤ Real.exp (-1) := by
  have hh : Real.exp (1/2 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have he : Real.exp 1 ≤ 4 := by
    rw [show (1 : ℝ) = 1/2+1/2 by ring,Real.exp_add]
    nlinarith [Real.exp_pos (1/2 : ℝ)]
  have hi : (1/4 : ℝ) ≤ 1/Real.exp 1 := (le_div_iff₀ (Real.exp_pos 1)).mpr (by linarith)
  simpa only [Real.exp_neg,one_div] using hi

theorem amplification_decay {L : ℝ} (hL : 1 ≤ L) :
    (1/4 : ℝ)^(amplificationCount L) ≤ Real.exp (-10*L) := by
  calc
    _ ≤ Real.exp (-1)^(amplificationCount L) := pow_le_pow_left₀ (by norm_num) quarter_le_exp_neg_one _
    _ = Real.exp (-(amplificationCount L : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [(amplification_bounds hL).2.1])

theorem polynomial_decay {L : ℝ} {n m : ℕ} (hL : cutoff n ≤ L) (hm : (m : ℝ) ≤ 130*L^n) :
    (4*(m : ℝ)+1)*Real.exp (-10*L) ≤ Real.exp (-2*L) := by
  have hL8 : 8 ≤ L := (cutoff_ge_eight n).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLn : 1 ≤ L^n := one_le_pow₀ hL1
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp : L^n ≤ (n.factorial : ℝ)*Real.exp L := by
    have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp L (by linarith : 0 ≤ L) n)
    nlinarith
  have hcoeff : 521*(n.factorial : ℝ) ≤ Real.exp (7*L) := by
    have hc : 521*(n.factorial : ℝ)+8 ≤ L := hL
    linarith [Real.add_one_le_exp (7*L)]
  calc
    _ ≤ (521*L^n)*Real.exp (-10*L) :=
      mul_le_mul_of_nonneg_right (by nlinarith : 4*(m : ℝ)+1 ≤ 521*L^n) (Real.exp_pos _).le
    _ ≤ (521*((n.factorial : ℝ)*Real.exp L))*Real.exp (-10*L) := by gcongr
    _ = (521*(n.factorial : ℝ))*(Real.exp L*Real.exp (-10*L)) := by ring
    _ = (521*(n.factorial : ℝ))*Real.exp (-9*L) := by rw [← Real.exp_add]; congr 1; congr 1; ring
    _ ≤ Real.exp (7*L)*Real.exp (-9*L) := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem double_decay_strict {L : ℝ} (hL : 8 ≤ L) : 2*Real.exp (-2*L) < Real.exp (-L)/2 := by
  have hs : Real.exp (-L) < 1/4 := by
    have hi : 1/Real.exp L < 1/4 := (div_lt_iff₀ (Real.exp_pos L)).mpr (by linarith [Real.add_one_le_exp L])
    simpa only [Real.exp_neg,one_div] using hi
  have he : Real.exp (-2*L) = (Real.exp (-L))^2 := by
    rw [show -2*L = (-L)+(-L) by ring,Real.exp_add,pow_two]
  rw [he]
  nlinarith [mul_pos (Real.exp_pos (-L)) (sub_pos.mpr hs)]

theorem mean_budget {L ε : ℝ} {n m : ℕ} (hL : cutoff n ≤ L) (hm : (m : ℝ) ≤ 130*L^n)
    (htail : 2*L ≤ (m : ℝ)*ε^2/64) :
    (copyCount m (amplificationCount L) : ℝ)*(1/5 : ℝ)^(amplificationCount L)+
      Real.exp (-((m : ℝ)*ε^2/64)) < Real.exp (-L)/2 := by
  have hL8 : 8 ≤ L := (cutoff_ge_eight n).trans hL
  have hl : (copyCount m (amplificationCount L) : ℝ)*(1/5 : ℝ)^(amplificationCount L) ≤ Real.exp (-2*L) := by
    calc
      _ ≤ (4*(m : ℝ)+1)*(1/4 : ℝ)^(amplificationCount L) := low_mass _ _
      _ ≤ (4*(m : ℝ)+1)*Real.exp (-10*L) :=
        mul_le_mul_of_nonneg_left (amplification_decay (by linarith)) (by positivity)
      _ ≤ _ := polynomial_decay hL hm
  have ht : Real.exp (-((m : ℝ)*ε^2/64)) ≤ Real.exp (-2*L) := Real.exp_le_exp.mpr (by linarith)
  exact (show _ ≤ 2*Real.exp (-2*L) from by linarith).trans_lt (double_decay_strict hL8)

end SemAC02.CoveringSampleParameters
end

section
-- Inlined Solutions.CoveringSizeParameters

set_option maxHeartbeats 2000000

open SemAC02.CoveringSampleParameters

namespace SemAC02.CoveringSizeParameters

theorem shifted_scale_bound {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d) :
    (3*ε/4)^(-1/((d : ℝ)-1)) ≤ 2*ε^(-1/((d : ℝ)-1)) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let e := 1/((d : ℝ)-1)
  have he : e ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < (d : ℝ)-1)).mpr (by linarith)
  have hexp : -1/((d : ℝ)-1) = -e := by dsimp [e]; ring
  rw [hexp,show 3*ε/4 = ε/(4/3) by ring,
    Real.div_rpow hε.le (by norm_num : (0 : ℝ) ≤ 4/3),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4/3),div_inv_eq_mul]
  have hb : (4/3 : ℝ)^e ≤ 2 :=
    (Real.rpow_le_self_of_one_le (by norm_num) he).trans (by norm_num)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hε.le (-e))

theorem dimension_exponential {L : ℝ} (hL : 1 ≤ L) {n m : ℕ} (hm : (m : ℝ) ≤ 130*L^n) :
    (m : ℝ) ≤ Real.exp (((n : ℝ)+130)*L) := by
  have hLin : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hp : L^n ≤ Real.exp ((n : ℝ)*L) := by
    calc
      _ ≤ Real.exp L ^ n := pow_le_pow_left₀ (by linarith) hLin n
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hc : (130 : ℝ) ≤ Real.exp (130*L) := by linarith [Real.add_one_le_exp (130*L)]
  calc
    _ ≤ 130*L^n := hm
    _ ≤ Real.exp (130*L)*Real.exp ((n : ℝ)*L) :=
      mul_le_mul hc hp (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem amplification_exponential {L : ℝ} (hL : 1 ≤ L) :
    (amplificationCount L : ℝ) ≤ Real.exp (11*L) := by
  have h := (amplification_bounds hL).2.2
  linarith [Real.add_one_le_exp (11*L)]

theorem copies_exponential {L : ℝ} (hL : 1 ≤ L) {n m : ℕ} (hm : (m : ℝ) ≤ 130*L^n) :
    (copyCount m (amplificationCount L) : ℝ) ≤ Real.exp (((n : ℝ)+146)*L) := by
  let t := amplificationCount L
  have ht : (t : ℝ) ≤ 11*L := (amplification_bounds hL).2.2
  have hpow : (5/4 : ℝ)^t ≤ Real.exp (11*L) := by
    calc
      _ ≤ Real.exp 1 ^ t := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) t
      _ = Real.exp (t : ℝ) := by rw [← Real.exp_nat_mul,mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr ht
  have hfour : (4 : ℝ) ≤ Real.exp (4*L) := by linarith [Real.add_one_le_exp (4*L)]
  have hproduct : 4*(m : ℝ)*(5/4 : ℝ)^t ≤ Real.exp (((n : ℝ)+145)*L) := by
    calc
      _ ≤ (Real.exp (4*L)*Real.exp (((n : ℝ)+130)*L))*Real.exp (11*L) :=
        mul_le_mul (mul_le_mul hfour (dimension_exponential hL hm) (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hpow (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have hs : (copyCount m t : ℝ) ≤ Real.exp (((n : ℝ)+145)*L)+1 := by
    have h := (copy_bounds m t).2
    linarith
  have hQ : 1 ≤ Real.exp (((n : ℝ)+145)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have hEL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ Real.exp (((n : ℝ)+145)*L)+1 := hs
    _ ≤ Real.exp (((n : ℝ)+145)*L)*Real.exp L := by nlinarith
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem total_size {L D A : ℝ} (hL : 1 ≤ L) (hD : 0 ≤ D) (hD' : D ≤ 2*L)
    {n m u v : ℕ} (hm : (m : ℝ) ≤ 130*L^n)
    (hu : (u : ℝ) ≤ (amplificationCount L : ℝ)*Real.exp (A*D))
    (hv : v ≤ 1+copyCount m (amplificationCount L)*u) :
    (v : ℝ) ≤ Real.exp (((n : ℝ)+158+2*abs A)*L) := by
  have hcoeff : A*D ≤ (2*abs A)*L := by
    calc
      _ ≤ (abs A)*D := mul_le_mul_of_nonneg_right (le_abs_self A) hD
      _ ≤ (abs A)*(2*L) := mul_le_mul_of_nonneg_left hD' (abs_nonneg A)
      _ = _ := by ring
  have hu' : (u : ℝ) ≤ Real.exp ((11+2*abs A)*L) := by
    calc
      _ ≤ (amplificationCount L : ℝ)*Real.exp (A*D) := hu
      _ ≤ Real.exp (11*L)*Real.exp ((2*abs A)*L) :=
        mul_le_mul (amplification_exponential hL) (Real.exp_le_exp.mpr hcoeff) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hprod : (copyCount m (amplificationCount L) : ℝ)*(u : ℝ) ≤
      Real.exp (((n : ℝ)+157+2*abs A)*L) := by
    calc
      _ ≤ Real.exp (((n : ℝ)+146)*L)*Real.exp ((11+2*abs A)*L) :=
        mul_le_mul (copies_exponential hL hm) hu' (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hv' : (v : ℝ) ≤ 1+(copyCount m (amplificationCount L) : ℝ)*(u : ℝ) := by exact_mod_cast hv
  have hQ : 1 ≤ Real.exp (((n : ℝ)+157+2*abs A)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have hEL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ 1+Real.exp (((n : ℝ)+157+2*abs A)*L) := by linarith
    _ ≤ Real.exp (((n : ℝ)+157+2*abs A)*L)*Real.exp L := by nlinarith
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SemAC02.CoveringSizeParameters
end

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

section
-- Inlined Theorems.Thm_SemAC02_theorem_8_9_coin_formulas
namespace SemAC02

/-- **Theorem 8.9 (Limaye et al. [52])** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Theorem 8.9, p.66): fix `d ≥ 2`.
For all sufficiently small `ϵ > 0`, there is a monotone AND/OR formula of depth at most `d` and
size `exp(O_d(ϵ^{−1/(d−1)}))` solving the `ϵ`-coin problem with error at most `1/10`.

The paper cites this result; its proof is in Limaye et al. [52].

**Formalization Note** `O_d(·)` is one constant `A` (depending on `d` only) chosen before
`ϵ`; "sufficiently small" is `∃ ϵ₀ > 0, ∀ ϵ ∈ (0, ϵ₀)`. The formula is a `Circ (Fin m)` on some
number `m` of inputs, in the paper's normal form (`IsReduced`); its size is the tree size. -/
theorem theorem_8_9_coin_formulas (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        IsCoinDistinguisher ε (1 / 10) (fun x => T.eval x) := by
  exact SemAC02.CoinFormulas.coin_formulas d hd

end SemAC02
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

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_10_shifted_distinguisher
namespace SemAC02

/-- **Lemma 8.10 (A shifted coin distinguisher)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.10, p.66): fix
`d ≥ 2`. For all sufficiently small `ϵ > 0`, there exist an integer `m ≥ 1` and a monotone,
AND-rooted formula `T` on `m` input variables, of depth at most `d` and size
`exp(O_d(ϵ^{−1/(d−1)}))`, such that
`Pr_{x∼Bern(1/2−ϵ)^m}[T(x) = 1] ≤ 1/5` and `Pr_{x∼Bern(1/2)^m}[T(x) = 0] ≤ 1/5`.

**Formalization Note** `O_d(·)` is one constant `A` chosen before `ϵ`; "sufficiently small" is
`∃ ϵ₀ > 0, ∀ ϵ ∈ (0, ϵ₀)`. AND-rooted: the root is an AND gate. The formula is in the paper's
normal form (`IsReduced`); size is tree size. -/
theorem lemma_8_10_shifted_distinguisher (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ 1 / 5 ∧
        bernProb (1 / 2) (fun x => !T.eval x) ≤ 1 / 5 := by
  exact SemAC02.ShiftedCoinDistinguisher.shifted_distinguisher d hd

end SemAC02
end

section
-- Inlined Solutions.CoinConjunctionAmplification

set_option maxHeartbeats 1000000

open SemAC02.CircuitRenaming SemAC02.ConjunctionCopies
open SemAC02.BernoulliProduct SemAC02.BernoulliAlgebra

namespace SemAC02.CoinConjunctionAmplification

theorem amplification (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ, 1 ≤ t →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ (t : ℝ) * Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        (4 / 5 : ℝ) ^ t ≤ bernProb (1 / 2) (fun x => T.eval x) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ (1 / 5 : ℝ) ^ t := by
  classical
  obtain ⟨A,ε₀,hε₀,hform⟩ := lemma_8_10_shifted_distinguisher d hd
  refine ⟨A,min ε₀ (1/2),lt_min hε₀ (by norm_num),?_⟩
  intro ε hε hsmall t ht
  have hcut := lt_min_iff.mp hsmall
  obtain ⟨m,hm,C,hM,hR,⟨cs,rfl⟩,hdepth,hsize,hlo,hhi⟩ := hform ε hε hcut.1
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin t) := ⟨⟨0,by omega⟩⟩
  let U := amplify t cs
  let e : Fin t × Fin m ≃ Fin (t*m) := finProdFinEquiv
  let T := U.rename e
  have hprob (p : ℝ) : bernProb p (fun x => T.eval x) =
      bernProb p (fun x => (Circ.and cs).eval x) ^ t := by
    calc
      _ = prob p (fun x : Fin (t*m) → Bool => U.eval (fun v => x (e v))) := by
        simp only [prob_fin,T,eval_rename,Function.comp_def]
      _ = prob p (fun x => U.eval x) := prob_equiv e p (fun x => U.eval x)
      _ = _ := prob_amplify p cs
  refine ⟨t*m,by nlinarith,T,monotone_rename e (monotone_amplify t hM),
    reduced_rename e e.injective (reduced_amplify t hR),?_,?_,?_,?_,?_⟩
  · exact ⟨((children t cs).dedup).map (Circ.rename e),by simp only [T,U,amplify,Circ.rename]⟩
  · exact (depth_rename e U).le.trans ((depth_amplify t cs).trans hdepth)
  · have hs : (T.treeSize : ℝ) ≤ (t : ℝ) * ((Circ.and cs).treeSize : ℝ) := by
      dsimp only [T]
      rw [size_rename]
      exact_mod_cast size_amplify ht cs
    exact hs.trans (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg t))
  · rw [hprob]
    apply pow_le_pow_left₀ (by norm_num)
    rw [prob_compl] at hhi
    linarith
  · rw [hprob]
    exact pow_le_pow_left₀ (prob_nonneg (by linarith : 0 ≤ 1/2-ε) (by linarith : 1/2-ε ≤ 1) _) hlo t

end SemAC02.CoinConjunctionAmplification
end

section
-- Inlined Theorems.Thm_SemAC02_Supplement_lemma_8_11_amplification
namespace SemAC02.Supplement

theorem lemma_8_11_amplification (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ, 1 ≤ t →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ (t : ℝ) * Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        (4 / 5 : ℝ) ^ t ≤ bernProb (1 / 2) (fun x => T.eval x) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ (1 / 5 : ℝ) ^ t := by
  exact SemAC02.CoinConjunctionAmplification.amplification d hd

end SemAC02.Supplement
end

section
-- Inlined Solutions.CoveringGadget

set_option maxHeartbeats 2000000

open SemAC02.CoveringSampleParameters

namespace SemAC02.CoveringGadget

theorem covering_gadget (d : ℕ) (hd : 2 ≤ d) :
    ∃ A B₁ B₂ ε₀ : ℝ, 0 < B₁ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ m : ℕ, Odd m →
      128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ) →
      (∀ m' : ℕ, Odd m' → 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m' : ℝ) → m ≤ m') →
      ∃ Cm : Circ (Fin m), IsMonotoneCirc Cm ∧ IsReduced Cm ∧ Cm.depth ≤ d+1 ∧
        (Cm.treeSize : ℝ) ≤ Real.exp (A*ε^(-1/((d : ℝ)-1))) ∧
        (∃ cs, Cm = Circ.or cs ∧ ∀ c ∈ cs, c.isAnd = true ∧ c.depth ≤ d) ∧
        (∀ x : Fin m → Bool, (m : ℝ)/2 ≤ (hammingWeight x : ℝ) → Cm.eval x = true) ∧
        bernProb (1/2-ε) (fun x => Cm.eval x) ≤ Real.exp (-(ε^(-1/((d : ℝ)-1)))) ∧
        B₁*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ B₂*(ε^(-1/((d : ℝ)-1)))^(2*d-1) := by
  classical
  obtain ⟨A,εa,hεa,hform⟩ := Supplement.lemma_8_11_amplification d hd
  let n := 2*d-1
  let K := cutoff n
  have hK8 : 8 ≤ K := cutoff_ge_eight n
  have hKpos : 0 < K := by linarith
  have hcutpos : 0 < 1/K^(d-1) := div_pos zero_lt_one (pow_pos hKpos _)
  refine ⟨(n : ℝ)+158+2*abs A,128,130,min εa (min (1/2) (1/K^(d-1))),by norm_num,
    lt_min hεa (lt_min (by norm_num) hcutpos),?_⟩
  intro ε hε hsmall m hm hml hmin
  have hc := lt_min_iff.mp hsmall
  have hc' := lt_min_iff.mp hc.2
  let L := ε^(-1/((d : ℝ)-1))
  have hLK : K ≤ L := CoveringDimension.small_parameter_scale hKpos hε hd hc'.2
  have hL1 : 1 ≤ L := by linarith
  obtain ⟨hmpos,hmupper⟩ := CoveringDimension.dimension_bounds hL1 n hm hml hmin
  have htail : 2*L ≤ (m : ℝ)*ε^2/64 := CoveringDimension.dimension_tail_exponent hε hd hml
  let t := amplificationCount L
  have ht : 1 ≤ t := (amplification_bounds hL1).1
  let δ := 3*ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ < εa := by dsimp [δ]; linarith [hc.1]
  obtain ⟨r,hr,C,hC,hR,⟨cs,hroot⟩,hdepth,hsize,hfair,hlow⟩ := hform δ hδ hδsmall t ht
  have hA : C.isAnd = true := by rw [hroot]; rfl
  have hbudget : (copyCount m t : ℝ)*(1/5 : ℝ)^t+Real.exp (-((m : ℝ)*ε^2/64)) < Real.exp (-L)/2 :=
    mean_budget hLK hmupper htail
  obtain ⟨Cm,hCm,hCmR,hCmdepth,hCmsize,hCmroot,hcover,hacc⟩ :=
    CoveringProbabilisticMethod.exists_cover (s := copyCount m t) hmpos hC hR hA hdepth hε hc'.1.le
      (show 0 ≤ (1/5 : ℝ)^t from by positivity) hfair hlow (coverage_mass m t) hbudget
  refine ⟨Cm,hCm,hCmR,hCmdepth,?_,hCmroot,hcover,hacc,hml,hmupper⟩
  exact CoveringSizeParameters.total_size hL1 (Real.rpow_nonneg hδ.le _)
    (CoveringSizeParameters.shifted_scale_bound hε hd) hmupper hsize hCmsize

end SemAC02.CoveringGadget
end

open SemAC02

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ A B₁ B₂ ε₀ : ℝ, 0 < B₁ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ m : ℕ, Odd m →
      128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m : ℝ) →
      (∀ m' : ℕ, Odd m' → 128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m' : ℝ) → m ≤ m') →
      ∃ Cm : Circ (Fin m), IsMonotoneCirc Cm ∧ IsReduced Cm ∧ Cm.depth ≤ d + 1 ∧
        (Cm.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        (∃ cs, Cm = Circ.or cs ∧ ∀ c ∈ cs, c.isAnd = true ∧ c.depth ≤ d) ∧
        (∀ x : Fin m → Bool, (m : ℝ) / 2 ≤ (hammingWeight x : ℝ) → Cm.eval x = true) ∧
        bernProb (1 / 2 - ε) (fun x => Cm.eval x) ≤ Real.exp (-(ε ^ (-1 / ((d : ℝ) - 1)))) ∧
        B₁ * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ B₂ * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1)  := by
  exact SemAC02.CoveringGadget.covering_gadget d hd
