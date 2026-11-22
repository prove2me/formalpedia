-- Prove2me | solution 1 for WeldedPath.crossing_probability_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-22T16:11:49.15932+00:00
-- url     : https://prove2.me/submissions/b04c07b1-855a-4770-8fd6-7e3e54347011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeldedPath_opTensor
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_Supplement_projGood
import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_exactCpO
import Mathlib.Analysis.CStarAlgebra.Basic
import Theorems.Thm_WeldedPath_Supplement_exact_query_goodness

set_option autoImplicit false

-- Solutions.WeldedPathCrossingScalar
section

namespace WeldedPath.CrossingScalar

open scoped BigOperators

/-- The scalar one-step error appearing in the good-space estimate. -/
noncomputable def stepError (n l t : ℕ) : ℝ :=
  Real.sqrt (1 / (2 : ℝ) ^ l + (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n)

theorem stepError_nonneg (n l t : ℕ) : 0 ≤ stepError n l t := Real.sqrt_nonneg _

theorem stepError_sq (n l t : ℕ) :
    stepError n l t ^ 2 = 1 / (2 : ℝ) ^ l +
      (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n := by
  exact Real.sq_sqrt (by positivity)

theorem stepError_mono (n l : ℕ) {s t : ℕ} (hst : s ≤ t) :
    stepError n l s ≤ stepError n l t := by
  apply Real.sqrt_le_sqrt
  gcongr

theorem stepError_sum_le (n l q : ℕ) :
    (∑ i ∈ Finset.range q, stepError n l (6 * i)) ≤
      (q : ℝ) * stepError n l (6 * q) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range q, stepError n l (6 * q) := by
      apply Finset.sum_le_sum
      intro i hi
      apply stepError_mono
      exact Nat.mul_le_mul_left 6 (Nat.le_of_lt (Finset.mem_range.mp hi))
    _ = _ := by simp

/-- A scalar recurrence suffices for accumulating the one-query leakage. -/
theorem recurrence_le (n l q : ℕ) (C : ℝ) (hC : 0 ≤ C) (a : ℕ → ℝ)
    (hzero : a 0 ≤ 0)
    (hstep : ∀ i < q, a (i + 1) ≤ a i + C * stepError n l (6 * i)) :
    a q ≤ C * (q : ℝ) * stepError n l (6 * q) := by
  have haux : ∀ j ≤ q, a j ≤ C * (j : ℝ) * stepError n l (6 * q) := by
    intro j
    induction j with
    | zero => simpa using hzero
    | succ j ih =>
      intro hj
      have hjq : j < q := by omega
      have hmono := stepError_mono n l (Nat.mul_le_mul_left 6 (Nat.le_of_lt hjq))
      have hmul := mul_le_mul_of_nonneg_left hmono hC
      have hprev := ih (Nat.le_of_lt hjq)
      have hnext := hstep j hjq
      push_cast
      nlinarith
  exact haux q le_rfl

/-- Squaring the accumulated error gives the desired quadratic/cubic bound,
with a single absolute factor seven. -/
theorem accumulated_stepError_sq_le (n l q : ℕ) (hq : 1 ≤ q) (C : ℝ) :
    (C * (q : ℝ) * stepError n l (6 * q)) ^ 2 ≤
      7 * C ^ 2 * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
        (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : (6 : ℝ) * q + 1 ≤ 7 * q := by linarith
  have hterm : (n : ℝ) * (6 * q + 1) / (2 : ℝ) ^ n ≤
      7 * (n : ℝ) * q / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hbase : 1 / (2 : ℝ) ^ l + (n : ℝ) * (6 * q + 1) / (2 : ℝ) ^ n ≤
      7 * (1 / (2 : ℝ) ^ l + (n : ℝ) * q / (2 : ℝ) ^ n) := by
    have he : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ l := by positivity
    have hterm' : (n : ℝ) * (6 * q + 1) / (2 : ℝ) ^ n ≤
        7 * ((n : ℝ) * q / (2 : ℝ) ^ n) := by
      convert hterm using 1 <;> ring
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (sq_nonneg C) (sq_nonneg (q : ℝ)))
  rw [mul_pow, mul_pow, stepError_sq]
  push_cast
  calc
    _ ≤ C ^ 2 * (q : ℝ) ^ 2 *
        (7 * (1 / (2 : ℝ) ^ l + (n : ℝ) * q / (2 : ℝ) ^ n)) := hmul
    _ = _ := by ring

theorem probability_of_amplitude_le (n l q : ℕ) (hq : 1 ≤ q)
    (C a p : ℝ) (ha : 0 ≤ a)
    (hp : p ≤ a ^ 2)
    (hamp : a ≤ C * (q : ℝ) * stepError n l (6 * q)) :
    p ≤ 7 * C ^ 2 * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
      (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  apply hp.trans
  apply (sq_le_sq₀ ha (ha.trans hamp)).mpr hamp |>.trans
  exact accumulated_stepError_sq_le n l q hq C

end WeldedPath.CrossingScalar

end

-- Solutions.WeldedPathLeakageTelescoping
section

namespace WeldedPath.LeakageTelescoping

open ContinuousLinearMap CrossingScalar

variable {X : Type*} [Fintype X]

/-- A single good-space leakage estimate propagates through an algorithm
operation commuting with the next good projector. -/
theorem one_step (P Q O U : Hil X →L[ℂ] Hil X) (ε : ℝ)
    (hO : ∀ ψ, ‖O ψ‖ ≤ ‖ψ‖) (hU : ∀ ψ, ‖U ψ‖ ≤ ‖ψ‖)
    (hQ : ∀ ψ, ‖(1 - Q) ψ‖ ≤ ‖ψ‖)
    (hcomm : Q.comp U = U.comp Q)
    (hleak : ∀ ψ, ‖(1 - Q) (O (P ψ))‖ ≤ ε * ‖ψ‖) (ψ : Hil X) :
    ‖(1 - Q) (U (O ψ))‖ ≤ ‖(1 - P) ψ‖ + ε * ‖ψ‖ := by
  have hcomm' : ∀ v, (1 - Q) (U v) = U ((1 - Q) v) := by
    intro v
    have he := congrArg (fun T : Hil X →L[ℂ] Hil X => T v) hcomm
    change U v - Q (U v) = U (v - Q v)
    rw [map_sub]
    exact congrArg (fun w => U v - w) he
  have hdec : O ψ = O ((1 - P) ψ) + O (P ψ) := by
    change O ψ = O (ψ - P ψ) + O (P ψ)
    rw [map_sub]
    abel
  calc
    _ = ‖U ((1 - Q) (O ψ))‖ := by rw [hcomm']
    _ ≤ ‖(1 - Q) (O ψ)‖ := hU _
    _ = ‖(1 - Q) (O ((1 - P) ψ)) + (1 - Q) (O (P ψ))‖ := by rw [hdec, map_add]
    _ ≤ ‖(1 - Q) (O ((1 - P) ψ))‖ + ‖(1 - Q) (O (P ψ))‖ := norm_add_le _ _
    _ ≤ ‖(1 - P) ψ‖ + ε * ‖ψ‖ := add_le_add ((hQ _).trans (hO _)) (hleak ψ)

/-- The quantitative error accumulation used by the crossing theorem. The
single-query hypothesis is kept explicit; this lemma proves the full
telescoping and final measurement argument, not that hypothesis. -/
theorem crossing_of_local_leakage (n l q : ℕ) (hq : 1 ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (state : Fin (q + 1) → Hil X)
    (P : Fin (q + 1) → Hil X →L[ℂ] Hil X)
    (U : Fin q → Hil X →L[ℂ] Hil X) (O E : Hil X →L[ℂ] Hil X)
    (hO : ∀ ψ, ‖O ψ‖ ≤ ‖ψ‖) (hU : ∀ i ψ, ‖U i ψ‖ ≤ ‖ψ‖)
    (hP : ∀ i ψ, ‖(1 - P i) ψ‖ ≤ ‖ψ‖)
    (hcomm : ∀ i, (P i.succ).comp (U i) = (U i).comp (P i.succ))
    (hstep : ∀ i, state i.succ = U i (O (state i.castSucc)))
    (hunit : ∀ i, ‖state i‖ ≤ 1)
    (hzero : P 0 (state 0) = state 0)
    (hleak : ∀ (i : Fin q) ψ, ‖(1 - P i.succ) (O (P i.castSucc ψ))‖ ≤
      C * stepError n l (6 * i.val) * ‖ψ‖)
    (hE : ∀ ψ, ‖E ψ‖ ≤ ‖ψ‖)
    (hEP : E.comp (P (Fin.last q)) = 0) :
    ‖E (state (Fin.last q))‖ ^ 2 ≤
      7 * C ^ 2 * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
        (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  have herr : ∀ i : Fin (q + 1),
      ‖(1 - P i) (state i)‖ ≤ C * (i.val : ℝ) * stepError n l (6 * q) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      change ‖state 0 - P 0 (state 0)‖ ≤ _
      simp [hzero]
    | succ i ih =>
      rw [hstep i]
      have hlocal := one_step (P i.castSucc) (P i.succ) O (U i)
        (C * stepError n l (6 * i.val)) hO (hU i) (hP i.succ) (hcomm i) (hleak i)
        (state i.castSucc)
      have hε : 0 ≤ C * stepError n l (6 * i.val) := mul_nonneg hC (stepError_nonneg _ _ _)
      have hu := mul_le_mul_of_nonneg_left (hunit i.castSucc) hε
      have hm := mul_le_mul_of_nonneg_left
        (stepError_mono n l (Nat.mul_le_mul_left 6 (Nat.le_of_lt i.isLt))) hC
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
      nlinarith
  have hfinal := herr (Fin.last q)
  have hmeasure : ‖E (state (Fin.last q))‖ ≤
      ‖(1 - P (Fin.last q)) (state (Fin.last q))‖ := by
    have hz := congrArg (fun T : Hil X →L[ℂ] Hil X => T (state (Fin.last q))) hEP
    have he : E ((1 - P (Fin.last q)) (state (Fin.last q))) = E (state (Fin.last q)) := by
      change E (state (Fin.last q) - P (Fin.last q) (state (Fin.last q))) = _
      rw [map_sub]
      change E (state (Fin.last q)) - _ = _
      rw [show E (P (Fin.last q) (state (Fin.last q))) = 0 from hz, sub_zero]
    rw [← he]
    exact hE _
  apply probability_of_amplitude_le n l q hq C
    ‖(1 - P (Fin.last q)) (state (Fin.last q))‖
    (‖E (state (Fin.last q))‖ ^ 2) (norm_nonneg _)
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmeasure
  · simpa only [Fin.val_last] using hfinal

end WeldedPath.LeakageTelescoping

end

-- Solutions.CompressedPermutationPrimitive
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem ketBra_eq_rankOne {X Y : Type*} [Fintype X] [Fintype Y]
    (u : Hil Y) (v : Hil X) : ketBra u v = InnerProductSpace.rankOne ℂ u v := rfl

theorem ket_inner {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    inner ℂ (ket x) (ket y) = if x = y then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem pCF_apply {X : Type*} [Fintype X] (u v w : Hil X) :
    pCF u v w = w - inner ℂ u w • u - inner ℂ v w • v +
      inner ℂ v w • u + inner ℂ u w • v := by
  rfl

theorem pCF_adjoint {X : Type*} [Fintype X] (u v : Hil X) :
    ContinuousLinearMap.adjoint (pCF u v) = pCF u v := by
  simp only [pCF, ketBra_eq_rankOne, map_add, map_sub,
    ContinuousLinearMap.adjoint_one, InnerProductSpace.adjoint_rankOne]
  abel

theorem pCF_involutive {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v).comp (pCF u v) = 1 := by
  have hvu : inner ℂ v u = 0 := by rw [← inner_conj_symm, huv]; simp
  have hleft (w : Hil X) : inner ℂ u (pCF u v w) = inner ℂ v w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hu, huv]
    ring
  have hright (w : Hil X) : inner ℂ v (pCF u v w) = inner ℂ u w := by
    rw [pCF_apply]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hv, hvu]
    ring
  apply ContinuousLinearMap.ext
  intro w
  change pCF u v (pCF u v w) = w
  rw [pCF_apply, hleft, hright, pCF_apply]
  module

theorem pCF_norm_map {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0)
    (w : Hil X) : ‖pCF u v w‖ = ‖w‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pCF u v)).mpr
  rw [pCF_adjoint, pCF_involutive u v hu hv huv]

theorem addPair_apply_self {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y x = some y := by
  simp [InjDb.addPair, hx, hy]

theorem addPair_injective {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    Set.InjOn (I.addPair x) {y | I.symm y = none} := by
  intro y hy z hz h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, addPair_apply_self I x z hx hz] at hh
  exact Option.some.inj hh

theorem addPair_ne {s : ℕ} (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) : I.addPair x y ≠ I := by
  intro h
  have hh := congrArg (fun J : InjDb s => J x) h
  rw [addPair_apply_self I x y hx hy, hx] at hh
  cases hh

theorem size_symm {s : ℕ} (I : InjDb s) : InjDb.size I.symm = I.size := by
  have hex (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :
      ∃ y, I x = some y := by
    cases h : I x with
    | none => simp [h] at hx
    | some y => exact ⟨y, rfl⟩
  let f (x : Fin s) (hx : x ∈ Finset.univ.filter fun x => (I x).isSome) :=
    (hex x hx).choose
  have hf x hx : I x = some (f x hx) := (hex x hx).choose_spec
  symm
  apply Finset.card_bij f
  · intro x hx
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    change I.symm (f x hx) = some x at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h]
    rfl
  · intro x hx y hy hxy
    have h := (I.inv x (f x hx)).mpr (hf x hx)
    have h' := (I.inv y (f y hy)).mpr (hf y hy)
    rw [hxy, h'] at h
    exact (Option.some.inj h).symm
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    cases h : I.symm y with
    | none => simp [h] at hy'
    | some x =>
      have hx : I x = some y := (I.inv x y).mp h
      have hxmem : x ∈ Finset.univ.filter fun x => (I x).isSome := by simp [hx]
      refine ⟨x, hxmem, ?_⟩
      exact Option.some.inj ((hf x hxmem).symm.trans hx)

theorem unused_card {s : ℕ} (I : InjDb s) :
    (Finset.univ.filter fun y => I.symm y = none).card = s - I.size := by
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun y : Fin s => (I.symm y).isSome)
  have hf : (Finset.univ.filter fun y : Fin s => ¬ (I.symm y).isSome) =
      (Finset.univ.filter fun y => I.symm y = none) := by
    ext y
    cases h : I.symm y <;> simp [h]
  rw [hf, Finset.card_univ, Fintype.card_fin] at hh
  change InjDb.size I.symm + _ = s at hh
  rw [size_symm] at hh
  omega

theorem size_lt_of_unset {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    I.size < s := by
  have hh := Finset.card_lt_card (Finset.filter_ssubset.mpr
    (show ∃ y ∈ (Finset.univ : Finset (Fin s)), ¬ (I y).isSome from
      ⟨x, Finset.mem_univ _, by simp [hx]⟩))
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using hh

theorem plus_sum_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y)) =
        ((s - I.size : ℕ) : ℂ) := by
  let D := Finset.univ.filter fun y => I.symm y = none
  have hsum : inner ℂ (∑ y ∈ D, ket (I.addPair x y))
      (∑ y ∈ D, ket (I.addPair x y)) = (D.card : ℂ) := by
    rw [sum_inner]
    calc
      _ = ∑ y ∈ D, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [inner_sum]
        simp only [ket_inner]
        rw [Finset.sum_eq_single y]
        · simp
        · intro z hz hzy
          apply if_neg
          intro heq
          exact hzy ((addPair_injective I x hx
            (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 heq).symm)
        · intro hnot
          exact (hnot hy).elim
      _ = _ := by simp
  simpa only [D, unused_card] using hsum

theorem plusState_inner_self {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (plusState I x) (plusState I x) = 1 := by
  have hm : 0 < ((s - I.size : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (size_lt_of_unset I x hx)
  have hs : Real.sqrt ((s - I.size : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hscalar : (Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ ^ 2 *
      ((s - I.size : ℕ) : ℝ) = 1 := by
    field_simp
    exact (Real.sq_sqrt hm.le).symm
  unfold plusState
  rw [inner_smul_left, inner_smul_right, plus_sum_inner_self I x hx]
  push_cast
  have hh : ((Real.sqrt ((s - I.size : ℕ) : ℝ) : ℂ)⁻¹) ^ 2 *
      ((s - I.size : ℕ) : ℂ) = 1 := by exact_mod_cast hscalar
  convert hh using 1
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem ket_inner_plusState {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none) :
    inner ℂ (ket I) (plusState I x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      inner ℂ (ket I) (ket (I.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    exact (addPair_ne I x y hx (Finset.mem_filter.mp hy).2).symm
  rw [hh, mul_zero]

theorem compressionPrimitive_norm {s : ℕ} (I : InjDb s) (x : Fin s) (hx : I x = none)
    (ψ : Hil (InjDb s)) : ‖pCF (plusState I x) (ket I) ψ‖ = ‖ψ‖ := by
  apply pCF_norm_map
  · exact plusState_inner_self I x hx
  · simp only [ket_inner, if_true]
  · rw [← inner_conj_symm, ket_inner_plusState I x hx]
    simp

end WeldedPath.CompressedPrimitive

end

-- Solutions.CompressedPermutationUnitary
section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

theorem addPair_apply_other {s : ℕ} (I : InjDb s) (x y u : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (hu : u ≠ x) :
    I.addPair x y u = I u := by
  simp [InjDb.addPair, hx, hy, hu]

theorem addPair_eq_original {s : ℕ} (I J : InjDb s) (x y z : Fin s)
    (hIx : I x = none) (hIy : I.symm y = none)
    (hJx : J x = none) (hJz : J.symm z = none)
    (h : I.addPair x y = J.addPair x z) : I = J := by
  apply PEquiv.ext
  intro u
  by_cases hu : u = x
  · simp only [hu, hIx, hJx]
  · have hh := congrArg (fun K : InjDb s => K u) h
    simpa only [addPair_apply_other I x y u hIx hIy hu,
      addPair_apply_other J x z u hJx hJz hu] using hh

theorem ket_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) :
    inner ℂ (ket I) (plusState J x) = 0 := by
  unfold plusState
  rw [inner_smul_right, inner_sum]
  have hh : (∑ y ∈ Finset.univ.filter (fun y => J.symm y = none),
      inner ℂ (ket I) (ket (J.addPair x y))) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [ket_inner, if_neg]
    intro heq
    have hh := congrArg (fun K : InjDb s => K x) heq
    rw [hIx, addPair_apply_self J x y hJx (Finset.mem_filter.mp hy).2] at hh
    cases hh
  rw [hh, mul_zero]

theorem plus_inner_plus_other {s : ℕ} (I J : InjDb s) (x : Fin s)
    (hIx : I x = none) (hJx : J x = none) (hIJ : I ≠ J) :
    inner ℂ (plusState I x) (plusState J x) = 0 := by
  have hsum : inner ℂ
      (∑ y ∈ Finset.univ.filter (fun y => I.symm y = none), ket (I.addPair x y))
      (∑ z ∈ Finset.univ.filter (fun z => J.symm z = none), ket (J.addPair x z)) = 0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro y hy
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro z hz
    rw [ket_inner, if_neg]
    exact fun h => hIJ (addPair_eq_original I J x y z hIx
      (Finset.mem_filter.mp hy).2 hJx (Finset.mem_filter.mp hz).2 h)
  simp only [plusState, inner_smul_left, inner_smul_right, hsum, mul_zero]

theorem pCF_delta (X : Type*) [Fintype X] (u v : Hil X) :
    pCF u v - 1 = -ketBra u u - ketBra v v + ketBra u v + ketBra v u := by
  unfold pCF
  abel

theorem pCF_delta_mul_zero {X : Type*} [Fintype X] (u v a b : Hil X)
    (hua : inner ℂ u a = 0) (hub : inner ℂ u b = 0)
    (hva : inner ℂ v a = 0) (hvb : inner ℂ v b = 0) :
    (pCF u v - 1) * (pCF a b - 1) = 0 := by
  rw [pCF_delta, pCF_delta]
  simp only [add_mul, sub_mul, neg_mul, mul_add, mul_sub, mul_neg,
    ketBra_eq_rankOne, ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    InnerProductSpace.rankOne_comp_rankOne,
    hua, hub, hva, hvb, zero_smul, neg_zero, sub_zero, add_zero]

theorem pCF_delta_square {X : Type*} [Fintype X] (u v : Hil X)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) (huv : inner ℂ u v = 0) :
    (pCF u v - 1) * (pCF u v - 1) = -((pCF u v - 1) + (pCF u v - 1)) := by
  have hh : pCF u v * pCF u v = 1 := pCF_involutive u v hu hv huv
  simp only [sub_mul, mul_sub, one_mul, mul_one, hh]
  abel

theorem compression_family_norm {X ι : Type*} [Fintype X] (S : Finset ι)
    (u v : ι → Hil X)
    (hu : ∀ i ∈ S, inner ℂ (u i) (u i) = 1)
    (hv : ∀ i ∈ S, inner ℂ (v i) (v i) = 1)
    (huv : ∀ i ∈ S, inner ℂ (u i) (v i) = 0)
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      inner ℂ (u i) (u j) = 0 ∧ inner ℂ (u i) (v j) = 0 ∧
      inner ℂ (v i) (u j) = 0 ∧ inner ℂ (v i) (v j) = 0)
    (ψ : Hil X) :
    ‖(1 + ∑ i ∈ S, (pCF (u i) (v i) - 1)) ψ‖ = ‖ψ‖ := by
  let Δ := fun i => pCF (u i) (v i) - 1
  have hdiag i (hi : i ∈ S) : Δ i * Δ i = -(Δ i + Δ i) :=
    pCF_delta_square (u i) (v i) (hu i hi) (hv i hi) (huv i hi)
  have hneq i (hi : i ∈ S) j (hj : j ∈ S) (hij : i ≠ j) : Δ i * Δ j = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hoff i hi j hj hij
    exact pCF_delta_mul_zero _ _ _ _ h₁ h₂ h₃ h₄
  have hsquare : (∑ i ∈ S, Δ i) * (∑ i ∈ S, Δ i) =
      -((∑ i ∈ S, Δ i) + (∑ i ∈ S, Δ i)) := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ i ∈ S, Δ i * Δ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact hneq i hi j hj hji.symm
        · intro hnot
          exact (hnot hi).elim
      _ = ∑ i ∈ S, -(Δ i + Δ i) := Finset.sum_congr rfl hdiag
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hinv : (1 + ∑ i ∈ S, Δ i) * (1 + ∑ i ∈ S, Δ i) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hsquare]
    abel
  have hadj : ContinuousLinearMap.adjoint (1 + ∑ i ∈ S, Δ i) =
      1 + ∑ i ∈ S, Δ i := by
    simp only [Δ, map_add, map_sum, map_sub, pCF_adjoint, ContinuousLinearMap.adjoint_one]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    (1 + ∑ i ∈ S, Δ i)).mpr
  rw [hadj]
  exact hinv

theorem pC_norm_map (s : ℕ) (x : Fin s) (ψ : Hil (InjDb s)) : ‖pC s x ψ‖ = ‖ψ‖ := by
  unfold pC
  apply compression_family_norm
  · intro I hI
    exact plusState_inner_self I x (Finset.mem_filter.mp hI).2
  · intro I _
    simp only [ket_inner, if_true]
  · intro I hI
    rw [← inner_conj_symm, ket_inner_plusState I x (Finset.mem_filter.mp hI).2]
    simp
  · intro I hI J hJ hIJ
    have hIx := (Finset.mem_filter.mp hI).2
    have hJx := (Finset.mem_filter.mp hJ).2
    refine ⟨plus_inner_plus_other I J x hIx hJx hIJ, ?_,
      ket_inner_plus_other I J x hIx hJx, ?_⟩
    · rw [← inner_conj_symm, ket_inner_plus_other J I x hJx hIx]
      simp
    · simp only [ket_inner, hIJ, if_false]

end WeldedPath.CompressedPrimitive

end

-- Solutions.WeldedPathHilbertSupport
section

namespace WeldedPath.HilbertSupport

open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem ketBra_apply (u : Hil Y) (v ψ : Hil X) :
    ketBra u v ψ = inner ℂ v ψ • u := rfl

theorem inner_ket [DecidableEq X] (x : X) (ψ : Hil X) :
    inner ℂ (ket x) ψ = ψ x := by
  simp [ket, EuclideanSpace.inner_single_left]

theorem ket_apply [DecidableEq X] (x y : X) :
    ket x y = if y = x then 1 else 0 := by
  simp [ket, PiLp.single_apply]

theorem ketTensor_apply (u : Hil A) (v : Hil X) (a : A) (x : X) :
    ketTensor u v (a, x) = u a * v x := rfl

theorem sum_basis [DecidableEq X] (ψ : Hil X) :
    (∑ x, ψ x • ket x) = ψ := by
  ext y
  simp [ket_apply]

theorem diagProj_apply [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) (x : X) :
    diagProj P ψ x = if P x then ψ x else 0 := by
  simp [diagProj, ketBra_apply, inner_ket, ket_apply]

theorem diagProj_zero_iff [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : diagProj P ψ = 0 ↔ ∀ x, P x → ψ x = 0 := by
  constructor
  · intro h x hx
    have he := congrArg (fun v : Hil X => v x) h
    simpa [diagProj_apply, hx] using he
  · intro h
    ext x
    by_cases hx : P x <;> simp [diagProj_apply, hx, h]

theorem diagProj_norm_le [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : ‖diagProj P ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x
  · simp [diagProj_apply, hx]
  · simp [diagProj_apply, hx]

theorem diagProj_ket [DecidableEq X] (P : X → Prop) [DecidablePred P] (x : X) :
    diagProj P (ket x) = if P x then ket x else 0 := by
  ext y
  by_cases hx : P x <;> by_cases hy : y = x <;>
    simp_all [diagProj_apply, ket_apply]

theorem opTensor_ket [DecidableEq A] [DecidableEq X]
    {B : Type*} [Fintype B] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y)
    (a : A) (x : X) :
    opTensor S T (ket (a, x)) = ketTensor (S (ket a)) (T (ket x)) := by
  simp [opTensor, ketBra_apply, inner_ket, ket_apply]

theorem tensor_ket_eq [DecidableEq A] [DecidableEq X] (a : A) (x : X) :
    ketTensor (ket a) (ket x) = ket (a, x) := by
  ext p
  obtain ⟨b, y⟩ := p
  by_cases ha : b = a <;> by_cases hx : y = x <;>
    simp [ketTensor_apply, ket_apply, ha, hx, Prod.mk.injEq]

theorem diagProj_tensor_zero [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (u : Hil A) (v : Hil X)
    (hv : ∀ x, P x → v x = 0) :
    diagProj (fun p : A × X => P p.2) (ketTensor u v) = 0 := by
  apply (diagProj_zero_iff _ _).mpr
  rintro ⟨a, x⟩ hx
  simp [ketTensor_apply, hv x hx]

theorem tensor_projector_annihilates [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (K : Submodule ℂ (Hil X))
    (hK : ∀ v ∈ K, ∀ x, P x → v x = 0) :
    (diagProj (fun p : A × X => P p.2)).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) K.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro p _
  rw [opTensor_ket]
  have hz := diagProj_tensor_zero P (ket p.1) (K.starProjection (ket p.2))
    (hK _ (K.starProjection_apply_mem _) )
  simpa using congrArg (fun v => ψ p • v) hz

end WeldedPath.HilbertSupport

end

-- Solutions.WeldedPathEncodedOracleUnitary
section

namespace WeldedPath.EncodedOracleUnitary

open Classical QAlgorithms HilbertSupport CompressedPrimitive Supplement
open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem basisMap_apply_equiv [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) (x : X) : basisMap e ψ (e x) = ψ x := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply, e.injective.eq_iff]

theorem basisMap_equiv_norm [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (ψ : Hil X) : ‖basisMap e ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← Equiv.sum_comp e (fun y => ‖basisMap e ψ y‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  rw [basisMap_apply_equiv]

theorem basisMap_involutive_norm [DecidableEq X]
    (f : X → X) (hf : Function.Involutive f) (ψ : Hil X) :
    ‖basisMap f ψ‖ = ‖ψ‖ :=
  basisMap_equiv_norm (hf.toPerm f) ψ

noncomputable def slice (ψ : Hil (A × X)) (a : A) : Hil X :=
  WithLp.toLp 2 (fun x => ψ (a, x))

theorem opTensor_one_apply [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (ψ : Hil (A × X)) (a : A) (y : Y) :
    opTensor (1 : Hil A →L[ℂ] Hil A) T ψ (a, y) = T (slice ψ a) y := by
  conv_rhs => rw [← sum_basis (slice ψ a)]
  simp [opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice]

theorem sum_slice_norm_sq (ψ : Hil (A × X)) :
    (∑ a, ‖slice ψ a‖ ^ 2) = ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, slice,
    PiLp.toLp_apply]

theorem opTensor_one_norm [DecidableEq A] [DecidableEq X]
    (T : Hil X →L[ℂ] Hil Y) (hT : ∀ ψ, ‖T ψ‖ = ‖ψ‖) (ψ : Hil (A × X)) :
    ‖opTensor (1 : Hil A →L[ℂ] Hil A) T ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_congr rfl
  intro a _
  have hs : slice (opTensor (1 : Hil A →L[ℂ] Hil A) T ψ) a = T (slice ψ a) := by
    ext y
    exact opTensor_one_apply T ψ a y
  rw [hs, hT]

theorem adjoint_norm_of_norm (U : Hil X →L[ℂ] Hil X)
    (hU : ∀ ψ, ‖U ψ‖ = ‖ψ‖) (ψ : Hil X) :
    ‖ContinuousLinearMap.adjoint U ψ‖ = ‖ψ‖ := by
  have he : (ContinuousLinearMap.adjoint U).comp U = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mp hU
  have hi : Function.LeftInverse (ContinuousLinearMap.adjoint U) U := by
    intro v
    exact congrArg (fun T : Hil X →L[ℂ] Hil X => T v) he
  have hsurj : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) hi.injective
  obtain ⟨v, rfl⟩ := hsurj ψ
  rw [hi v, hU v]

theorem qubits_add_cancel {d : ℕ} (a b : Qubits d) : a + b + b = a := by
  funext i
  change a i + b i + b i = a i
  cases a i <;> cases b i <;> rfl

theorem stdQueryE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × Equiv.Perm (Fin s))) :
    ‖stdQueryE enc x inv ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, π⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

theorem purifiedXorE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (ψ : Hil (Qubits d × InjDb s)) :
    ‖purifiedXorE enc x ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, I⟩
  cases h : I x with
  | none => simp only [h]
  | some y => simp only [h, qubits_add_cancel]

theorem flipDb_norm (s : ℕ) (ψ : Hil (InjDb s)) : ‖flipDb s ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  exact PEquiv.symm_symm

theorem cpOE_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ = ‖ψ‖ := by
  let pc := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (pC s x)
  let fl := opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (flipDb s)
  have hpc : ∀ v, ‖pc v‖ = ‖v‖ := opTensor_one_norm (pC s x) (pC_norm_map s x)
  have hfl : ∀ v, ‖fl v‖ = ‖v‖ := opTensor_one_norm (flipDb s) (flipDb_norm s)
  have hpc' : ∀ v, ‖ContinuousLinearMap.adjoint pc v‖ = ‖v‖ :=
    adjoint_norm_of_norm pc hpc
  have hfl' : ∀ v, ‖ContinuousLinearMap.adjoint fl v‖ = ‖v‖ :=
    adjoint_norm_of_norm fl hfl
  change ‖(if inv then fl.comp
    ((pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))).comp
      (ContinuousLinearMap.adjoint fl))
    else pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))) ψ‖ = _
  cases inv <;> simp only [Bool.false_eq_true, if_false, if_true,
    ContinuousLinearMap.comp_apply, hpc, hfl, purifiedXorE_norm, hpc', hfl']

theorem cpOE_adjoint_norm {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖ContinuousLinearMap.adjoint (cpOE enc x inv) ψ‖ = ‖ψ‖ :=
  adjoint_norm_of_norm _ (cpOE_norm enc x inv) ψ

theorem cpOE_norm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖cpOE enc x inv ψ‖ ≤ ‖ψ‖ := (cpOE_norm enc x inv ψ).le

end WeldedPath.EncodedOracleUnitary

end

-- Solutions.WeldedPathControlledOperators
section

namespace WeldedPath.ControlledOperators

open Classical HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X]

theorem controlled_apply (T : C → Hil X →L[ℂ] Hil Y)
    (ψ : Hil (C × X)) (c : C) (y : Y) :
    controlled T ψ (c, y) = T c (slice ψ c) y := by
  conv_rhs => rw [← sum_basis (slice ψ c)]
  simp [controlled, opTensor, ketBra_apply, inner_ket, ketTensor_apply,
    Fintype.sum_prod_type, ket_apply, slice, apply_ite, ite_apply]

theorem controlled_norm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) (ψ : Hil (C × X)) :
    ‖controlled T ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← sum_slice_norm_sq, ← sum_slice_norm_sq]
  apply Finset.sum_le_sum
  intro c _
  have hs : slice (controlled T ψ) c = T c (slice ψ c) := by
    ext y
    exact controlled_apply T ψ c y
  rw [hs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT c _)

theorem controlled_opNorm_le (T : C → Hil X →L[ℂ] Hil Y)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ ‖ψ‖) : ‖controlled T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using controlled_norm_le T hT ψ

end WeldedPath.ControlledOperators

end

-- Solutions.WeldedPathRegisterTransport
section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]

theorem ofBasis_ket {Y : Type*} [Fintype Y] (f : Ω → Hil Y) (p : Ω) :
    ofBasis f (ket p) = f p := by
  simp [ofBasis, ketBra_apply, inner_ket, ket_apply]

theorem basisMap_ket {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : Ω → Y) (p : Ω) : basisMap f (ket p) = ket (f p) := by
  simp [basisMap, ketBra_apply, inner_ket, ket_apply]

theorem partImg_one (x : X) (f : X → Ω) :
    partImg (1 : Hil X →L[ℂ] Hil X) x f = ket (f x) := by
  simp [partImg, inner_ket, ket_apply]

theorem partImg_basisMap (x : X) (f : X → X) (put : X → Ω) :
    partImg (basisMap f) x put = ket (put (f x)) := by
  simp [partImg, basisMap_ket, inner_ket, ket_apply]

theorem controlled_ket (T : C → Hil X →L[ℂ] Hil X) (c : C) (x : X) :
    controlled T (ket (c, x)) = ketTensor (ket c) (T c (ket x)) := by
  have hs (a : C) : slice (ket (c, x)) a = if a = c then ket x else 0 := by
    ext y
    by_cases ha : a = c <;> simp [slice, ket_apply, ha, Prod.mk.injEq]
  ext ⟨a, y⟩
  rw [controlled_apply, hs]
  by_cases ha : a = c
  · subst a
    simp [ketTensor_apply, ket_apply]
  · simp [ha, ketTensor_apply, ket_apply]

theorem partImg_reindex (e : Ω ≃ C × X) (T : Hil X →L[ℂ] Hil X)
    (c : C) (x : X) :
    basisMap e (partImg T x (fun y => e.symm (c, y))) =
      ketTensor (ket c) (T (ket x)) := by
  simp only [partImg, map_sum, map_smul, basisMap_ket, Equiv.apply_symm_apply, inner_ket]
  ext ⟨a, y⟩
  by_cases ha : a = c <;> simp [ketTensor_apply, ket_apply, Prod.mk.injEq, ha]

/-- Relabeling the coordinates of a controlled contraction preserves its
norm bound. The conclusion is expressed in the canonical `ofBasis` and
`partImg` syntax used by the welded-tree oracle registers. -/
theorem ofBasis_partImg_norm_le (e : Ω ≃ C × X)
    (T : C → Hil X →L[ℂ] Hil X) (hT : ∀ c x, ‖T c x‖ ≤ ‖x‖)
    (ψ : Hil Ω) :
    ‖ofBasis (fun p => partImg (T (e p).1) (e p).2
      (fun x => e.symm ((e p).1, x))) ψ‖ ≤ ‖ψ‖ := by
  let U := ofBasis (fun p => partImg (T (e p).1) (e p).2
    (fun x => e.symm ((e p).1, x)))
  have heq : basisMap e (U ψ) = controlled T (basisMap e ψ) := by
    rw [← sum_basis ψ]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    change basisMap e (ofBasis _ (ket p)) = controlled T (basisMap e (ket p))
    rw [ofBasis_ket, basisMap_ket, partImg_reindex]
    exact (controlled_ket T (e p).1 (e p).2).symm
  change ‖U ψ‖ ≤ ‖ψ‖
  rw [← basisMap_equiv_norm e (U ψ), heq, ← basisMap_equiv_norm e ψ]
  exact controlled_norm_le T hT _

end WeldedPath.RegisterTransport

end

-- Solutions.WeldedPathQueryRunContraction
section

namespace WeldedPath.QueryRunContraction

open Classical QAlgorithms Supplement HilbertSupport RegisterTransport
open scoped BigOperators

variable {A D : Type*} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D]

noncomputable def matrixOp (M : Matrix A A ℂ) : Hil A →L[ℂ] Hil A :=
  ofBasis fun a => act M (ket a)

theorem matrixOp_apply (M : Matrix A A ℂ) (ψ : Hil A) : matrixOp M ψ = act M ψ := by
  ext a
  simp [matrixOp, ofBasis, ketBra_apply, inner_ket, act, Matrix.mulVec,
    dotProduct, ket_apply, mul_comm]

theorem matrixOp_norm (M : Matrix A A ℂ) (hM : M ∈ Matrix.unitaryGroup A ℂ) (ψ : Hil A) :
    ‖matrixOp M ψ‖ = ‖ψ‖ := by
  rw [matrixOp_apply]
  exact act_norm_of_mem_unitaryGroup hM ψ

theorem partImg_put_left (T : Hil A →L[ℂ] Hil A) (a : A) (d : D) :
    partImg T a (fun a' => (a', d)) = ketTensor (T (ket a)) (ket d) := by
  ext ⟨b, e⟩
  by_cases he : e = d <;>
    simp [partImg, inner_ket, ketTensor_apply, ket_apply, Prod.mk.injEq, he]

theorem ketTensor_ket_norm (ψ : Hil A) (d : D) : ‖ketTensor ψ (ket d)‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ = ∑ a : A, ∑ e : D, ‖ketTensor ψ (ket d) (a, e)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    _ = ∑ a : A, ‖ψ a‖ ^ 2 := by simp [ketTensor_apply, ket_apply, apply_ite]
    _ = _ := (EuclideanSpace.norm_sq_eq ψ).symm

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W]

theorem liftAlgU_norm_le (M : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ)
    (hM : M ∈ Matrix.unitaryGroup ((ι × κ) × W) ℂ)
    (ψ : Hil (((ι × κ) × W) × D)) : ‖liftAlgU M ψ‖ ≤ ‖ψ‖ := by
  have he : liftAlgU (D := D) M = ofBasis (fun p =>
      partImg (matrixOp M) p.1 (fun a => (a, p.2))) := by
    unfold liftAlgU
    congr 1
    funext p
    rw [partImg_put_left, matrixOp_apply]
  rw [he]
  exact ofBasis_partImg_norm_le (Equiv.prodComm ((ι × κ) × W) D)
    (fun _ => matrixOp M) (fun _ φ => (matrixOp_norm M hM φ).le) ψ

noncomputable def oracleEquiv : (((ι × κ) × W) × D) ≃ W × ((ι × κ) × D) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun p := ((p.2.1, p.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem liftOracle_norm_le (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (hO : ∀ ψ, ‖O ψ‖ ≤ ‖ψ‖) (ψ : Hil (((ι × κ) × W) × D)) :
    ‖liftOracle O ψ‖ ≤ ‖ψ‖ :=
  ofBasis_partImg_norm_le oracleEquiv (fun _ => O) (fun _ => hO) ψ

theorem stateAtDb_norm_le {q : ℕ} (alg : QueryAlg ι κ W q)
    (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (hO : ∀ ψ, ‖O ψ‖ ≤ ‖ψ‖) (d₀ : D) (i : Fin (q + 1)) :
    ‖stateAtDb alg O d₀ i‖ ≤ 1 := by
  induction i using Fin.induction with
  | zero =>
    simp only [stateAtDb, Fin.induction_zero]
    exact (liftAlgU_norm_le _ (alg.U 0).property _).trans (by
      rw [ketTensor_ket_norm, alg.start_unit])
  | succ i ih =>
    simp only [stateAtDb, Fin.induction_succ]
    exact (liftAlgU_norm_le _ (alg.U i.succ).property _).trans
      ((liftOracle_norm_le O hO _).trans ih)

theorem finalStateDb_norm_le {q : ℕ} (alg : QueryAlg ι κ W q)
    (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (hO : ∀ ψ, ‖O ψ‖ ≤ ‖ψ‖) (d₀ : D) : ‖finalStateDb alg O d₀‖ ≤ 1 :=
  stateAtDb_norm_le alg O hO d₀ (Fin.last q)

end WeldedPath.QueryRunContraction

end

-- Solutions.WeldedPathTensorOperators
section

namespace WeldedPath.TensorOperators

open Classical EncodedOracleUnitary HilbertSupport
open scoped BigOperators

variable {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq A] [DecidableEq X] [DecidableEq Y]

lemma slice_opTensor_one (T : Hil X →L[ℂ] Hil Y) (ψ : Hil (A × X)) (a : A) :
    slice (opTensor (1 : Hil A →L[ℂ] Hil A) T ψ) a = T (slice ψ a) := by
  ext y
  exact opTensor_one_apply T ψ a y

lemma opTensor_one_comp (S : Hil Y →L[ℂ] Hil Z) (T : Hil X →L[ℂ] Hil Y) :
    (opTensor (1 : Hil A →L[ℂ] Hil A) S).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) T) =
      opTensor (1 : Hil A →L[ℂ] Hil A) (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨a, y⟩
  simp only [ContinuousLinearMap.comp_apply, opTensor_one_apply, slice_opTensor_one]

lemma inner_ketTensor_slice (a : A) (v : Hil X) (ψ : Hil (A × X)) :
    inner ℂ (ketTensor (ket a) v) ψ = inner ℂ v (slice ψ a) := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, ketTensor_apply, ket_apply, slice,
    apply_ite, mul_ite]

lemma adjoint_opTensor_one_apply (T : Hil X →L[ℂ] Hil Y)
    (ψ : Hil (A × Y)) (a : A) (x : X) :
    ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) T) ψ (a, x) =
      ContinuousLinearMap.adjoint T (slice ψ a) x := by
  rw [← inner_ket (a, x), ContinuousLinearMap.adjoint_inner_right, opTensor_ket]
  simp only [ContinuousLinearMap.one_apply]
  rw [inner_ketTensor_slice, ← ContinuousLinearMap.adjoint_inner_right, inner_ket]

lemma adjoint_opTensor_one (T : Hil X →L[ℂ] Hil Y) :
    ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) T) =
      opTensor (1 : Hil A →L[ℂ] Hil A) (ContinuousLinearMap.adjoint T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨a, x⟩
  rw [adjoint_opTensor_one_apply, opTensor_one_apply]

theorem opTensor_one_partial (V : Hil X →L[ℂ] Hil Y)
    (hV : (V.comp (ContinuousLinearMap.adjoint V)).comp V = V) :
    (((opTensor (1 : Hil A →L[ℂ] Hil A) V).comp
      (ContinuousLinearMap.adjoint (opTensor (1 : Hil A →L[ℂ] Hil A) V))).comp
        (opTensor (1 : Hil A →L[ℂ] Hil A) V)) =
        opTensor (1 : Hil A →L[ℂ] Hil A) V := by
  rw [adjoint_opTensor_one, opTensor_one_comp, opTensor_one_comp, hV]

end WeldedPath.TensorOperators

end

-- Solutions.WeldedPathGoodEmpty
section

namespace WeldedPath.GoodEmpty

open Classical Supplement
open scoped BigOperators

def emptyForest (n : ℕ) : AbsForest n where
  k := 0
  E := ∅
  color := fun p => Fin.elim0 p.1
  lab := Fin.elim0

def emptyDescription (n : ℕ) : Description n where
  H := emptyForest n
  sel := ∅
  ϕ₀ := Fin.elim0

theorem emptyForest_valid (n : ℕ) : (emptyForest n).IsValid := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [emptyForest]
  · intro v
    exact Fin.elim0 v
  · simp [emptyForest]
  · intro u
    exact Fin.elim0 u
  · intro u
    exact Fin.elim0 u

theorem emptyDescription_valid (n : ℕ) : (emptyDescription n).IsValid := by
  refine ⟨emptyForest_valid n, ?_⟩
  intro u
  exact Fin.elim0 u

theorem emptyForest_records (n : ℕ) : (emptyForest n).records = 0 := by
  simp only [AbsForest.records, emptyForest, Finset.card_empty, zero_add]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u
  exact Fin.elim0 u

theorem empty_muRef {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (ϕ : Fin (emptyForest n).k → Label n) : (emptyForest n).muRef l G ϕ = 1 := by
  unfold AbsForest.muRef
  apply Finset.prod_eq_one
  intro s _
  exact Fin.elim0 s

theorem empty_good {n : ℕ} (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (ϕ : Fin (emptyDescription n).H.k → Label n) :
    (emptyDescription n).IsGood l G B ϕ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : (emptyDescription n).H.muRef l G ϕ = 1 := empty_muRef l G ϕ
    exact he.symm ▸ (by norm_num : (0 : ℝ) < 1)
  · intro s
    exact Fin.elim0 s
  · intro s
    exact Fin.elim0 s
  · intro u
    exact Fin.elim0 u

theorem empty_isDbOf_iff {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (ϕ : Fin (emptyForest n).k → Label n) (I : Db l G) :
    (emptyForest n).IsDbOf l G ϕ I ↔ I = emptyDb l G := by
  constructor
  · intro h
    apply Prod.ext
    · apply PEquiv.ext
      intro i
      change I.1 i = none
      cases hi : I.1 i with
      | none => rfl
      | some j =>
        obtain ⟨u, _⟩ := (h.1 i j).mp hi
        exact Fin.elim0 u
    · funext b
      apply PEquiv.ext
      intro j
      change I.2 b j = none
      cases hj : I.2 b j with
      | none => rfl
      | some j' =>
        obtain ⟨p, hp, _⟩ := (h.2 b j j').mp hj
        exact (Finset.notMem_empty p hp).elim
  · rintro rfl
    constructor
    · intro i j
      simp [emptyDb, emptyForest]
    · intro b j j'
      simp [emptyDb, emptyForest]

theorem empty_gVec {n : ℕ} (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :
    (emptyDescription n).gVec l G B = ket (emptyDb l G) := by
  unfold Description.gVec
  simp only [empty_good, Finset.filter_true]
  change (∑ ϕ : Fin (emptyForest n).k → Label n,
    ((Real.sqrt ((emptyForest n).muRef l G ϕ) : ℝ) : ℂ) •
      ∑ I ∈ Finset.univ.filter (fun I => (emptyForest n).IsDbOf l G ϕ I), ket I) = _
  simp only [empty_muRef, Real.sqrt_one, Complex.ofReal_one, one_smul, empty_isDbOf_iff]
  have hfilter : (Finset.univ.filter fun I : Db l G => I = emptyDb l G) =
      {emptyDb l G} := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have hcard : Fintype.card (Fin (emptyForest n).k → Label n) = 1 := by
    rw [Fintype.card_fun]
    change Fintype.card (Label n) ^ Fintype.card (Fin 0) = 1
    simp
  rw [hfilter]
  simp only [Finset.sum_singleton, Finset.sum_const, Finset.card_univ, hcard, one_nsmul]

theorem empty_mem_goodSpace {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (B : Finset ℕ) (t : ℕ) : ket (emptyDb l G) ∈ goodSpace l G B t := by
  rw [← empty_gVec l G B]
  apply Submodule.subset_span
  refine ⟨emptyDescription n, emptyDescription_valid n, ?_, rfl⟩
  change (emptyForest n).records ≤ t
  rw [emptyForest_records]
  exact Nat.zero_le t

theorem good_starProjection_empty {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (B : Finset ℕ) (t : ℕ) :
    (goodSpace l G B t).starProjection (ket (emptyDb l G)) = ket (emptyDb l G) :=
  (goodSpace l G B t).starProjection_eq_self_iff.mpr (empty_mem_goodSpace l G B t)

end WeldedPath.GoodEmpty

end

-- Solutions.WeldedPathGraphDepth
section

namespace WeldedPath.LoopProof

lemma pow_root_ge_two (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  have h := Nat.two_pow_pos n
  rw [pow_succ]
  omega

lemma numV_eq (n : ℕ) : numV n = 2 * (2 ^ (n + 1) - 1) := by
  have h := pow_root_ge_two n
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma col_zero (n : ℕ) : col n 0 = 0 := by
  have h := pow_root_ge_two n
  simp [col, show 0 < 2 ^ (n + 1) - 1 by omega]

lemma col_exit (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma log_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) :
    Nat.log 2 (v + 1) ≤ n := by
  have h : v + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : v + 1 ≠ 0)).2 h
  omega

lemma log_right_le (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) ≤ n := by
  have hn := pow_root_ge_two n
  rw [IsVertex, numV_eq] at hv
  have h : v - (2 ^ (n + 1) - 1) + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2)
    (by omega : v - (2 ^ (n + 1) - 1) + 1 ≠ 0)).2 h
  omega

lemma col_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) : col n v ≤ n := by
  simpa [col, hv] using log_left_le n v hv

lemma col_right_ge (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    n + 1 ≤ col n v := by
  have hd := log_right_le n v hv hr
  simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1)]
  omega

lemma col_bounds (n v : ℕ) (hv : IsVertex n v) : col n v ≤ 2 * n + 1 := by
  by_cases h : v < 2 ^ (n + 1) - 1
  · have := col_left_le n v h
    omega
  · simp only [col, if_neg h]
    omega

lemma parent_spec {n v p : ℕ} (hp : parent n v = some p) :
    IsVertex n v ∧ IsVertex n p ∧
      ((col n p + 1 = col n v ∧ col n v ≤ n) ∨
        (col n v + 1 = col n p ∧ n + 1 ≤ col n v)) := by
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    have hv := h.1
    have hvleft : v < 2 ^ (n + 1) - 1 := by
      by_contra hh
      have := col_right_ge n v hv (by omega)
      omega
    have hvpos : 1 ≤ v := by
      by_contra hh
      have heq : v = 0 := by omega
      subst v
      simp [col_zero] at h
    have hpval : p = (v - 1) / 2 := by simpa using hp.symm
    have hpv : p < v := by omega
    have hpV : IsVertex n p := by unfold IsVertex at *; omega
    have hpleft : p < 2 ^ (n + 1) - 1 := by omega
    have hdiv : p + 1 = (v + 1) / 2 := by omega
    have hlog : Nat.log 2 (p + 1) = Nat.log 2 (v + 1) - 1 := by
      rw [hdiv, Nat.log_div_base]
    have hcols : col n p + 1 = col n v := by
      simp only [col, if_pos hvleft] at h
      simp only [col, if_pos hpleft, if_pos hvleft]
      omega
    exact ⟨hv, hpV, Or.inl ⟨hcols, h.2.2⟩⟩
  next h =>
    split at hp
    next h' =>
      have hv := h'.1
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc : col n v = 2 * n + 1 := by
          simpa [heq, exitIdx] using col_exit n
        omega
      have hvbig : 2 ^ (n + 1) ≤ v := by omega
      have hpval : p = (v - 2 ^ (n + 1)) / 2 + 2 ^ (n + 1) - 1 := by
        simpa using hp.symm
      have hpv : p < v := by omega
      have hpV : IsVertex n p := by unfold IsVertex at *; omega
      have hpright : 2 ^ (n + 1) - 1 ≤ p := by omega
      have hdiv : p - (2 ^ (n + 1) - 1) + 1 =
          (v - (2 ^ (n + 1) - 1) + 1) / 2 := by omega
      have hlog : Nat.log 2 (p - (2 ^ (n + 1) - 1) + 1) =
          Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) - 1 := by
        rw [hdiv, Nat.log_div_base]
      have hd := log_right_le n v hv hvright
      have hdpos : 1 ≤ Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) := by
        have := Nat.log_pos (by decide : 1 < 2)
          (show 2 ≤ v - (2 ^ (n + 1) - 1) + 1 by omega)
        omega
      have hcols : col n v + 1 = col n p := by
        simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1),
          if_neg (by omega : ¬ p < 2 ^ (n + 1) - 1)]
        omega
      exact ⟨hv, hpV, Or.inr ⟨hcols, h'.2.1⟩⟩
    next h' => simp at hp

lemma parent_eq_exit_imp {n v : ℕ} (hp : parent n v = some (exitIdx n)) :
    v = 2 ^ (n + 1) ∨ v = 2 ^ (n + 1) + 1 := by
  have hs := parent_spec hp
  have hc := col_exit n
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    rcases hs.2.2 with hleft | hright <;> omega
  next h =>
    split at hp
    next h' =>
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc' : col n v = 2 * n + 1 := by simpa [heq, exitIdx] using col_exit n
        omega
      simp only [Option.some.injEq, exitIdx] at hp
      omega
    next h' => simp at hp

lemma tree_mem_iff {n : ℕ} {G : WeldedInstance n} {v : ℕ} :
    Edge.tree v ∈ G.edges ↔ IsVertex n v ∧ (parent n v).isSome := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges, IsVertex]

lemma weld_mem_iff {n : ℕ} {G : WeldedInstance n} {u w : ℕ} :
    Edge.weld u w ∈ G.edges ↔ (u, w) ∈ G.weld := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges]

lemma edge_endpoints {n : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e : Edge} (he : e ∈ G.edges) :
    IsVertex n e.tail ∧ IsVertex n (e.head n) ∧
      (col n e.tail + 1 = col n (e.head n) ∨ col n (e.head n) + 1 = col n e.tail) := by
  cases e with
  | tree v =>
    have hv := tree_mem_iff.mp he
    cases hp : parent n v with
    | none => simp [hp] at hv
    | some p =>
      have hs := parent_spec hp
      simp only [Edge.tail, Edge.head, hp, Option.getD_some]
      exact ⟨hs.1, hs.2.1, hs.2.2.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)⟩
  | weld u w =>
    have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
    dsimp only at hw
    simp only [Edge.tail, Edge.head]
    exact ⟨hw.1, hw.2.2.1, Or.inl (by omega)⟩

lemma tree_head_col {n : ℕ} {G : WeldedInstance n} {v : ℕ}
    (he : Edge.tree v ∈ G.edges) :
    col n ((Edge.tree v).head n) = if col n v ≤ n then col n v - 1 else col n v + 1 := by
  have hv := tree_mem_iff.mp he
  cases hp : parent n v with
  | none => simp [hp] at hv
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    rcases hs with h | h
    · rw [if_pos h.2]
      omega
    · rw [if_neg (by omega : ¬ col n v ≤ n)]
      omega

lemma same_class_cols {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e e' : Edge} (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hclass : G.bEdge l e = G.bEdge l e') (hnone : G.bEdge l e ≠ none) :
    col n e.tail = col n e'.tail ∧ col n (e.head n) = col n (e'.head n) := by
  cases e with
  | tree v =>
    have hv : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      simp only [WeldedInstance.bEdge, if_neg h, ne_eq, not_true_eq_false] at hnone
    cases e' with
    | tree w =>
      have hw : n - l ≤ col n w ∧ col n w ≤ n + l := by
        by_contra h
        simp only [WeldedInstance.bEdge, if_pos hv, if_neg h, reduceCtorEq] at hclass
      have hc : col n v = col n w := by
        have hboth : col n v = col n w ∧ G.color (.tree v) = G.color (.tree w) := by
          simpa only [WeldedInstance.bEdge, if_pos hv, if_pos hw,
            Option.some.injEq, EdgeClass.tr.injEq] using hclass
        exact hboth.1
      refine ⟨hc, ?_⟩
      rw [tree_head_col he, tree_head_col he', hc]
    | weld u w => simp [WeldedInstance.bEdge, hv] at hclass
  | weld u w =>
    cases e' with
    | tree v =>
      simp only [WeldedInstance.bEdge] at hclass
      split at hclass <;> simp_all
    | weld u' w' =>
      have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
      have hw' := hG.1.1 (u', w') (weld_mem_iff.mp he')
      dsimp only at hw hw'
      simp only [Edge.tail, Edge.head]
      exact ⟨by omega, by omega⟩

end WeldedPath.LoopProof

end

-- Solutions.WeldedPathCrossingExclusion
section

namespace WeldedPath.Supplement.CrossingExclusion

open WeldedInstance InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_preserves {X : Type*} {J : SimpleGraph X} (P : X → Prop)
    (h : ∀ u v, J.Adj u v → (P u ↔ P v)) {u v : X} (hr : J.Reachable u v) :
    P u ↔ P v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons huv _ ih => exact (h _ _ huv).trans ih

lemma edge_adj (H : AbsForest n) (hH : H.IsValid) {p : Fin H.k × Fin H.k}
    (hp : p ∈ H.E) : H.graph.Adj p.1 p.2 := by
  exact ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩

lemma comp_root_exists (H : AbsForest n) (u : Fin H.k) :
    ∃ s, H.IsCompRoot s ∧ H.graph.Reachable s u := by
  classical
  have hu : u ∈ H.comp u := by simp [AbsForest.comp]
  let s := (H.comp u).min' ⟨u, hu⟩
  have hs : H.graph.Reachable u s := (Finset.mem_filter.mp
    (Finset.min'_mem (H.comp u) ⟨u, hu⟩)).2
  refine ⟨s, ?_, hs.symm⟩
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans hv⟩)

lemma edge_kappa_ne_zero (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0)
    {p : Fin H.k × Fin H.k} (hp : p ∈ H.E) :
    kappa l G (H.color p) (ϕ p.1).1 (ϕ p.2).1 ≠ 0 := by
  classical
  obtain ⟨s, hs, hsu⟩ := comp_root_exists H p.1
  have hsu' : p.1 ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  have hsv : p.2 ∈ H.comp s := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hsu.trans (edge_adj H hH hp).reachable⟩
  have hcard : (H.comp s).card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have h1 : p.1 = a := by simpa only [ha, Finset.mem_singleton] using hsu'
    have h2 : p.2 = a := by simpa only [ha, Finset.mem_singleton] using hsv
    have heq : p.1 = p.2 := h1.trans h2.symm
    exact (ne_of_lt (hH.1 p hp)) heq
  have hc : H.muComp l G s ϕ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hmu) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  unfold AbsForest.muComp at hc
  dsimp only at hc
  rw [if_neg hcard] at hc
  split at hc
  · have hw := (mul_ne_zero_iff.mp hc).2
    exact (Finset.prod_ne_zero_iff.mp hw) p (Finset.mem_filter.mpr ⟨hp, hsu'⟩)
  · exact False.elim (hc rfl)

lemma permData_orientation {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) :
    (t = true → u = e.1.tail) ∧ (t = false → u = e.1.head n) := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        rename_i e' he' hh
        have hi := (Classical.choose_spec hh.2).2.2
        constructor
        · intro ht
          simpa using ht
        · intro ht
          have hnt : u ≠ e'.tail := by simpa using ht
          exact hi.resolve_left hnt
      · simp at h

lemma class_pair_half (hG : G.IsValid) {e e' : Edge}
    (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hc : G.bEdge l e = G.bEdge l e') (hne : G.bEdge l e ≠ none) :
    IsVertex n e.tail ∧ IsVertex n (e'.head n) ∧
      ((col n e.tail ≤ n ↔ col n (e'.head n) ≤ n) ∨
        (e.tail ∈ Vweld n ∧ e'.head n ∈ Vweld n)) := by
  have hends := LoopProof.edge_endpoints hG he
  have hends' := LoopProof.edge_endpoints hG he'
  have hcols := LoopProof.same_class_cols hG he he' hc hne
  refine ⟨hends.1, hends'.2.1, ?_⟩
  cases e with
  | tree v =>
    left
    rw [← hcols.2, LoopProof.tree_head_col he]
    simp only [Edge.tail]
    split <;> omega
  | weld u w =>
    right
    have hw := hG.1.1 (u, w) (LoopProof.weld_mem_iff.mp he)
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, Or.inl hw.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hends'.2.1,
        Or.inr (by simpa only [Edge.head] using hcols.2.symm.trans hw.2.2.2)⟩

lemma kappa_half (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) :
    (col n u ≤ n ↔ col n v ≤ n) ∨ (u ∈ Vweld n ∧ v ∈ Vweld n) := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := permData_orientation hpd
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (fun g => g.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    have he := Finset.mem_filter.mp e.2
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.1 ht]
      exact (class_pair_half hG he.1 he'.1 (he.2.trans he'.2.symm)
        (by simp [he.2])).2.2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.2 ht]
      rcases (class_pair_half hG he'.1 he.1 (he'.2.trans he.2.symm)
        (by simp [he'.2])).2.2 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm

lemma tree_reachable_half (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0) {u v : Fin H.k}
    (hr : (H.treeGraph ϕ).Reachable u v) :
    col n (ϕ u).1 ≤ n ↔ col n (ϕ v).1 ≤ n := by
  apply reachable_preserves (fun u => col n (ϕ u).1 ≤ n) _ hr
  intro a b hab
  rcases hab.2 with ⟨he, hn⟩ | ⟨he, hn⟩
  · exact (kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn
  · exact ((kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn).symm

lemma recorded_adj_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) {I : Db l G} (hI : H.IsDbOf l G ϕ I)
    {a c : ℕ} (hac : (recordedGraph l G I.2).Adj a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
  have one : ∀ a c, (∃ (b : PClass n l) (j j' : Fin (classSize l G b)),
      I.2 b j = some j' ∧ a = ((edgeIdx l G b).symm j).1.tail ∧
      c = ((edgeIdx l G b).symm j').1.head n) →
      ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
    rintro a c ⟨b, j, j', hj, rfl, rfl⟩
    obtain ⟨p, hp, h⟩ := (hI.2 b j j').mp hj
    dsimp only at h
    rcases h with h | h
    · exact ⟨p.1, p.2, h.2.2.1, h.2.2.2, edge_adj H hH hp⟩
    · exact ⟨p.2, p.1, h.2.2.1, h.2.2.2, (edge_adj H hH hp).symm⟩
  rcases hac.2 with h | h
  · exact one _ _ h
  · obtain ⟨u, v, hu, hv, huv⟩ := one _ _ h
    exact ⟨v, u, hv, hu, huv.symm⟩

lemma recorded_reachable_lift_from (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ}
    (hac : (recordedGraph l G I.2).Reachable a c)
    (u : Fin H.k) (hu : (ϕ u).1 = a) :
    ∃ v, (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  induction w generalizing u with
  | nil => exact ⟨u, hu, .refl _⟩
  | cons hab w ih =>
    obtain ⟨x, y, hx, hy, hxy⟩ := recorded_adj_lift H hH ϕ hI hab
    have hux : u = x := hinj (Fin.ext (hu.trans hx.symm))
    obtain ⟨v, hv, hyv⟩ := ih y hy
    subst x
    exact ⟨v, hv, hxy.reachable.trans hyv⟩

lemma recorded_reachable_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ} (hne : a ≠ c)
    (hac : (recordedGraph l G I.2).Reachable a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons hab w =>
    obtain ⟨u, y, hu, hy, huy⟩ := recorded_adj_lift H hH ϕ hI hab
    obtain ⟨v, hv, hyv⟩ := recorded_reachable_lift_from H hH ϕ hinj hI w.reachable y hy
    exact ⟨u, v, hu, hv, huy.reachable.trans hyv⟩

lemma good_database_not_crossing (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (D : Description n) (hD : D.IsValid) (ϕ : Fin D.H.k → Label n)
    (hg : D.IsGood l G (Vbd n l) ϕ) (I : Db l G) (hI : D.H.IsDbOf l G ϕ I) :
    ¬ HasCrossing l G I.2 := by
  classical
  rintro ⟨a, c, ha, hacol, hc, hccol, hr⟩
  have hne : a ≠ c := by intro h; subst c; omega
  obtain ⟨u, v, hu, hv, huv⟩ := recorded_reachable_lift D.H hD.1 ϕ hg.2.2.2 hI hne hr
  obtain ⟨s, hs, _⟩ := hD.2 u
  have hsu := hs.2.symm
  have hsv := hsu.trans huv
  have hub : (ϕ u).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hu] using Finset.mem_range.mpr ha,
      Or.inl (by simpa only [hu] using hacol)⟩
  have hvb : (ϕ v).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hv] using Finset.mem_range.mpr hc,
      Or.inr (Or.inr (Or.inr (by simpa only [hv] using hccol)))⟩
  have hut : u ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 u hsu h hub
  have hvt : v ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 v hsv h hvb
  have htree : (D.H.treeGraph ϕ).Reachable u v :=
    (Finset.mem_filter.mp hut).2.symm.trans (Finset.mem_filter.mp hvt).2
  have hhalf := tree_reachable_half hG D.H hD.1 ϕ (ne_of_gt hg.1) htree
  rw [hu, hv, hacol, hccol] at hhalf
  omega

end WeldedPath.Supplement.CrossingExclusion

end

-- Solutions.WeldedPathGoodSupport
section

namespace WeldedPath.Supplement.CrossingSupport

open Classical HilbertSupport
open scoped BigOperators

set_option maxHeartbeats 400000

variable {n l : ℕ} {G : WeldedInstance n}

theorem gVec_coordinate_zero (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (D : Description n) (hD : D.IsValid) (I : Db l G)
    (hI : HasCrossing l G I.2) : D.gVec l G (Vbd n l) I = 0 := by
  have hterm (ϕ : Fin D.H.k → Label n) (hϕ : D.IsGood l G (Vbd n l) ϕ) :
      (∑ J ∈ Finset.univ.filter (fun J => D.H.IsDbOf l G ϕ J), ket J) I = 0 := by
    have hn : ¬ D.H.IsDbOf l G ϕ I := fun hi =>
      CrossingExclusion.good_database_not_crossing hG hl hln D hD ϕ hϕ I hi hI
    simp [ket_apply, hn]
  simp only [Description.gVec]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_eq_zero
  intro ϕ hϕ
  have he := hterm ϕ (Finset.mem_filter.mp hϕ).2
  simp only [WithLp.ofLp_sum, Finset.sum_apply] at he
  rw [he]
  simp

theorem goodSpace_coordinate_zero (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (t : ℕ) (v : Hil (Db l G)) (hv : v ∈ goodSpace l G (Vbd n l) t)
    (I : Db l G) (hI : HasCrossing l G I.2) : v I = 0 := by
  let K : Submodule ℂ (Hil (Db l G)) :=
    { carrier := {v | v I = 0}
      zero_mem' := rfl
      add_mem' := by intro u v hu hv; change u I + v I = 0; rw [hu, hv]; simp
      smul_mem' := by intro c v hv; change c • v I = 0; rw [hv]; simp }
  have hspan : goodSpace l G (Vbd n l) t ≤ K := by
    apply Submodule.span_le.mpr
    rintro v ⟨D, hD, _, rfl⟩
    exact gVec_coordinate_zero hG hl hln D hD I hI
  exact hspan hv

theorem crossing_good_projector_zero (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (A : Type*) [Fintype A] [DecidableEq A] (t : ℕ) :
    (diagProj (fun p : A × Db l G => HasCrossing l G p.2.2)).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A)
        (goodSpace l G (Vbd n l) t).starProjection) = 0 := by
  apply tensor_projector_annihilates (fun I : Db l G => HasCrossing l G I.2)
    (goodSpace l G (Vbd n l) t)
  intro v hv I hI
  exact goodSpace_coordinate_zero hG hl hln t v hv I hI

end WeldedPath.Supplement.CrossingSupport

end

-- Solutions.WeldedPathRunProjection
section

namespace WeldedPath.RunProjection

open Classical QAlgorithms Supplement HilbertSupport RegisterTransport
open QueryRunContraction EncodedOracleUnitary ControlledOperators TensorOperators
open scoped BigOperators

variable {A D : Type*} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D]

theorem controlled_const (T : Hil D →L[ℂ] Hil D) :
    controlled (fun _ : A => T) = opTensor (1 : Hil A →L[ℂ] Hil A) T := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨a, d⟩
  rw [controlled_apply, opTensor_one_apply]

theorem opTensor_one_norm_le (T : Hil D →L[ℂ] Hil D)
    (hT : ∀ ψ, ‖T ψ‖ ≤ ‖ψ‖) (ψ : Hil (A × D)) :
    ‖opTensor (1 : Hil A →L[ℂ] Hil A) T ψ‖ ≤ ‖ψ‖ := by
  rw [← controlled_const]
  exact controlled_norm_le _ (fun _ => hT) ψ

theorem opTensor_one_sub (T : Hil D →L[ℂ] Hil D) :
    (1 : Hil (A × D) →L[ℂ] Hil (A × D)) - opTensor 1 T = opTensor 1 (1 - T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨a, d⟩
  simp only [ContinuousLinearMap.sub_apply, one_apply_eq_self, PiLp.sub_apply,
    opTensor_one_apply]
  rfl

theorem opTensor_one_ketTensor (T : Hil D →L[ℂ] Hil D) (u : Hil A) (v : Hil D) :
    opTensor (1 : Hil A →L[ℂ] Hil A) T (ketTensor u v) = ketTensor u (T v) := by
  have hs (a : A) : slice (ketTensor u v) a = u a • v := by
    ext d
    rfl
  ext ⟨a, d⟩
  rw [opTensor_one_apply, hs, map_smul]
  rfl

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W]

theorem liftAlgU_apply (M : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ)
    (ψ : Hil (((ι × κ) × W) × D)) (a : (ι × κ) × W) (d : D) :
    liftAlgU M ψ (a, d) = ∑ b, M a b * ψ (b, d) := by
  simp [liftAlgU, ofBasis, ketBra_apply, inner_ket, ketTensor_apply, act,
    Matrix.mulVec, dotProduct, ket_apply, Fintype.sum_prod_type, apply_ite, mul_comm]

theorem slice_liftAlgU (M : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ)
    (ψ : Hil (((ι × κ) × W) × D)) (a : (ι × κ) × W) :
    slice (liftAlgU M ψ) a = ∑ b, M a b • slice ψ b := by
  ext d
  change liftAlgU M ψ (a, d) = _
  rw [liftAlgU_apply]
  simp [slice]

theorem dbOp_commutes_liftAlgU (M : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ)
    (T : Hil D →L[ℂ] Hil D) :
    (opTensor (1 : Hil ((ι × κ) × W) →L[ℂ] Hil ((ι × κ) × W)) T).comp (liftAlgU M) =
      (liftAlgU M).comp (opTensor (1 : Hil ((ι × κ) × W) →L[ℂ] Hil ((ι × κ) × W)) T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨a, d⟩
  simp only [ContinuousLinearMap.comp_apply, opTensor_one_apply, slice_liftAlgU,
    map_sum, map_smul, liftAlgU_apply, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]

noncomputable def oracleSlice (ψ : Hil (((ι × κ) × W) × D)) (w : W) :
    Hil ((ι × κ) × D) := WithLp.toLp 2 (fun p => ψ ((p.1, w), p.2))

theorem liftOracle_apply (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (ψ : Hil (((ι × κ) × W) × D)) (a : ι × κ) (w : W) (d : D) :
    liftOracle O ψ ((a, w), d) = O (oracleSlice ψ w) (a, d) := by
  rcases a with ⟨a₁, a₂⟩
  conv_rhs => rw [← sum_basis (oracleSlice ψ w)]
  simp [liftOracle, ofBasis, partImg, ketBra_apply, inner_ket, ket_apply,
    Fintype.sum_prod_type, oracleSlice, apply_ite, Prod.mk.injEq, ite_and,
    Finset.sum_ite_irrel]

theorem oracleSlice_liftOracle (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (ψ : Hil (((ι × κ) × W) × D)) (w : W) :
    oracleSlice (liftOracle O ψ) w = O (oracleSlice ψ w) := by
  ext ⟨a, d⟩
  exact liftOracle_apply O ψ a w d

theorem liftOracle_comp (S T : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D)) :
    (liftOracle (W := W) S).comp (liftOracle T) = liftOracle (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨⟨a, w⟩, d⟩
  simp only [ContinuousLinearMap.comp_apply, liftOracle_apply, oracleSlice_liftOracle]

theorem liftOracle_one_sub (T : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D)) :
    (1 : Hil (((ι × κ) × W) × D) →L[ℂ] Hil (((ι × κ) × W) × D)) - liftOracle T =
      liftOracle (1 - T) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨⟨a, w⟩, d⟩
  simp only [ContinuousLinearMap.sub_apply, one_apply_eq_self, PiLp.sub_apply, liftOracle_apply]
  rfl

theorem liftOracle_dbOp (T : Hil D →L[ℂ] Hil D) :
    liftOracle (W := W) (opTensor (1 : Hil (ι × κ) →L[ℂ] Hil (ι × κ)) T) =
      opTensor (1 : Hil ((ι × κ) × W) →L[ℂ] Hil ((ι × κ) × W)) T := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext ⟨⟨a, w⟩, d⟩
  rw [liftOracle_apply, opTensor_one_apply, opTensor_one_apply]
  rfl

end WeldedPath.RunProjection

end

-- Solutions.WeldedPathBoundedControl
section

namespace WeldedPath.BoundedControl

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open RegisterTransport QueryRunContraction
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]

theorem controlled_norm_bound (T : C → Hil X →L[ℂ] Hil X) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ c ψ, ‖T c ψ‖ ≤ K * ‖ψ‖) (ψ : Hil (C × X)) :
    ‖controlled T ψ‖ ≤ K * ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  calc
    _ = ∑ c, ‖T c (slice ψ c)‖ ^ 2 := by
      rw [← sum_slice_norm_sq]
      apply Finset.sum_congr rfl
      intro c _
      congr 2
      ext x
      exact controlled_apply T ψ c x
    _ ≤ ∑ c, (K * ‖slice ψ c‖) ^ 2 := Finset.sum_le_sum fun c _ =>
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr (hT c _)
    _ = K ^ 2 * ‖ψ‖ ^ 2 := by
      simp only [mul_pow]
      rw [← Finset.mul_sum, sum_slice_norm_sq]
    _ = _ := by ring

theorem ofBasis_partImg_norm_bound (e : Ω ≃ C × X)
    (T : C → Hil X →L[ℂ] Hil X) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ c x, ‖T c x‖ ≤ K * ‖x‖) (ψ : Hil Ω) :
    ‖ofBasis (fun p => partImg (T (e p).1) (e p).2
      (fun x => e.symm ((e p).1, x))) ψ‖ ≤ K * ‖ψ‖ := by
  let U := ofBasis (fun p => partImg (T (e p).1) (e p).2
    (fun x => e.symm ((e p).1, x)))
  have heq : basisMap e (U ψ) = controlled T (basisMap e ψ) := by
    rw [← sum_basis ψ]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    change basisMap e (ofBasis _ (ket p)) = controlled T (basisMap e (ket p))
    rw [ofBasis_ket, basisMap_ket, partImg_reindex]
    exact (controlled_ket T (e p).1 (e p).2).symm
  change ‖U ψ‖ ≤ K * ‖ψ‖
  rw [← basisMap_equiv_norm e (U ψ), heq, ← basisMap_equiv_norm e ψ]
  exact controlled_norm_bound T K hK hT _

theorem liftOracle_norm_bound {ι κ W D : Type*}
    [Fintype ι] [Fintype κ] [Fintype W] [Fintype D]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq W] [DecidableEq D]
    (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D))
    (K : ℝ) (hK : 0 ≤ K) (hO : ∀ ψ, ‖O ψ‖ ≤ K * ‖ψ‖)
    (ψ : Hil (((ι × κ) × W) × D)) : ‖liftOracle O ψ‖ ≤ K * ‖ψ‖ :=
  ofBasis_partImg_norm_bound oracleEquiv (fun _ => O) K hK (fun _ => hO) ψ

end WeldedPath.BoundedControl

end

-- Solutions.WeldedPathOperatorPolar
section

namespace WeldedPath.OperatorPolar

open scoped BigOperators
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma inv_sqrt_scalar (x : ℝ) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = (Real.sqrt x)⁻¹ := by
  by_cases hx : x ≤ 0
  · simp [Real.sqrt_eq_zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    have hh : (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x = 1 := by
      rw [← mul_inv, ← pow_two, Real.sq_sqrt hx'.le, inv_mul_cancel₀ (ne_of_gt hx')]
    rw [hh, one_mul]

noncomputable def invSqrt (A : Hil X →L[ℂ] Hil X) : Hil X →L[ℂ] Hil X :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

lemma invSqrt_adjoint (A : Hil X →L[ℂ] Hil X) :
    ContinuousLinearMap.adjoint (invSqrt A) = invSqrt A := by
  change star (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A) = _
  rw [← cfc_star]
  simp only [star_trivial]
  rfl

lemma invSqrt_sandwich (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A * invSqrt A * A * invSqrt A = invSqrt A := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  by_cases hf : ContinuousOn f (spectrum ℝ A)
  · have hff := cfc_mul f f A hf hf
    have hffi := cfc_mul (fun x => f x * f x) (fun x : ℝ => x) A
      (hf.mul hf) continuousOn_id
    have hffif := cfc_mul (fun x => f x * f x * x) f A
      ((hf.mul hf).mul continuousOn_id) hf
    calc
      _ = cfc (fun x => f x * f x * x * f x) A := by
        rw [hffif, hffi, hff, cfc_id' ℝ A hA]
        rfl
      _ = _ := cfc_congr (fun x _ => inv_sqrt_scalar x)
  · have hz : invSqrt A = 0 := cfc_apply_of_not_continuousOn A hf
    simp only [hz, zero_mul, mul_zero]

lemma invSqrt_commute (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    Commute (invSqrt A) A := by
  have h := cfc_commute_cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) A
  rwa [cfc_id' ℝ A hA] at h

lemma invSqrt_range_factor (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A) :
    invSqrt A = A * invSqrt A * invSqrt A * invSqrt A := by
  have hc := (invSqrt_commute A hA).eq
  calc
    _ = invSqrt A * invSqrt A * A * invSqrt A := (invSqrt_sandwich A hA).symm
    _ = invSqrt A * (invSqrt A * A) * invSqrt A := by simp only [mul_assoc]
    _ = invSqrt A * (A * invSqrt A) * invSqrt A := by rw [hc]
    _ = (invSqrt A * A) * invSqrt A * invSqrt A := by simp only [mul_assoc]
    _ = _ := by rw [hc]

lemma invSqrt_mapsTo (A : Hil X →L[ℂ] Hil X) (hA : IsSelfAdjoint A)
    (K : Submodule ℂ (Hil X)) (hK : ∀ ψ, A ψ ∈ K) (ψ : Hil X) :
    invSqrt A ψ ∈ K := by
  rw [invSqrt_range_factor A hA]
  exact hK _

noncomputable def polarMap (T : Hil X →L[ℂ] Hil Y) : Hil Y →L[ℂ] Hil X :=
  (ContinuousLinearMap.adjoint T).comp (invSqrt (T.comp (ContinuousLinearMap.adjoint T)))

lemma gram_selfadjoint (T : Hil X →L[ℂ] Hil Y) :
    IsSelfAdjoint (T.comp (ContinuousLinearMap.adjoint T)) := by
  change ContinuousLinearMap.adjoint (T.comp (ContinuousLinearMap.adjoint T)) = _
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem polarMap_partial (T : Hil X →L[ℂ] Hil Y) :
    ((polarMap T).comp (ContinuousLinearMap.adjoint (polarMap T))).comp (polarMap T) =
      polarMap T := by
  let B := invSqrt (T.comp (ContinuousLinearMap.adjoint T))
  have hB : ((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B = B := by
    exact invSqrt_sandwich _ (gram_selfadjoint T)
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change (((ContinuousLinearMap.adjoint T).comp B).comp
    (B.comp T)).comp ((ContinuousLinearMap.adjoint T).comp B) =
      (ContinuousLinearMap.adjoint T).comp B
  calc
    _ = (ContinuousLinearMap.adjoint T).comp
        (((B.comp B).comp (T.comp (ContinuousLinearMap.adjoint T))).comp B) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hB]

end WeldedPath.OperatorPolar

end

-- Solutions.WeldedPathCompletionLevels
section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}

theorem size_le (I : InjDb s) : I.size ≤ s := by
  simpa only [InjDb.size, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun x => (I x).isSome) Finset.univ))

theorem exists_unset (I : InjDb s) (hI : I.size < s) : ∃ x, I x = none := by
  by_contra! hn
  have hall : ∀ x, (I x).isSome := by
    intro x
    cases h : I x with
    | none => exact (hn x h).elim
    | some y => rfl
  have heq : I.size = s := by simp [InjDb.size, hall]
  omega

theorem size_addPair (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) :
    (I.addPair x y).size = I.size + 1 := by
  have hset : (Finset.univ.filter fun u => ((I.addPair x y) u).isSome) =
      insert x (Finset.univ.filter fun u => (I u).isSome) := by
    ext u
    by_cases hu : u = x
    · subst u
      simp [InjDb.addPair, hx, hy]
    · simp [InjDb.addPair, hx, hy, hu]
  have hnot : x ∉ Finset.univ.filter (fun u => (I u).isSome) := by simp [hx]
  exact (congrArg Finset.card hset).trans (Finset.card_insert_of_notMem hnot)

theorem unused_of_extends (I : InjDb s) (x : Fin s) (hx : I x = none)
    (φ : Equiv.Perm (Fin s)) (hφ : Extends φ I) : I.symm (φ x) = none := by
  cases h : I.symm (φ x) with
  | none => rfl
  | some z =>
    have hz : I z = some (φ x) := (I.inv z (φ x)).mp h
    have heq : z = x := φ.injective (hφ z (φ x) hz)
    subst z
    rw [hx] at hz
    cases hz

theorem extends_addPair_iff (I : InjDb s) (x y : Fin s)
    (hx : I x = none) (hy : I.symm y = none) (φ : Equiv.Perm (Fin s)) :
    Extends φ (I.addPair x y) ↔ Extends φ I ∧ φ x = y := by
  constructor
  · intro h
    refine ⟨?_, h x y (CompressedPrimitive.addPair_apply_self I x y hx hy)⟩
    intro u v huv
    have hux : u ≠ x := by
      intro heq
      subst u
      rw [hx] at huv
      cases huv
    exact h u v (by simp [InjDb.addPair, hx, hy, hux, huv])
  · rintro ⟨h, heq⟩ u v huv
    by_cases hux : u = x
    · subst u
      have hv : y = v := by simpa [InjDb.addPair, hx, hy] using huv
      exact heq.trans hv
    · exact h u v (by simpa [InjDb.addPair, hx, hy, hux] using huv)

noncomputable def rawCompletion (I : InjDb s) : Hil (Equiv.Perm (Fin s)) :=
  ∑ φ ∈ Finset.univ.filter (fun φ : Equiv.Perm (Fin s) => Extends φ I), ket φ

theorem rawCompletion_apply (I : InjDb s) (φ : Equiv.Perm (Fin s)) :
    rawCompletion I φ = if Extends φ I then 1 else 0 := by
  simp [rawCompletion, HilbertSupport.ket_apply]

theorem completion_mem_iff (M : Submodule ℂ (Hil (Equiv.Perm (Fin s))))
    (I : InjDb s) : completion I ∈ M ↔ rawCompletion I ∈ M := by
  have hpos : 0 < Real.sqrt (((s - I.size).factorial : ℕ) : ℝ) := by positivity
  have hnz : (((Real.sqrt ((s - I.size).factorial : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (ne_of_gt hpos)
  apply M.smul_mem_iff
  simpa only [Complex.ofReal_inv] using hnz

theorem rawCompletion_extension (I : InjDb s) (x : Fin s) (hx : I x = none) :
    rawCompletion I = ∑ y ∈ Finset.univ.filter (fun y => I.symm y = none),
      rawCompletion (I.addPair x y) := by
  ext φ
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawCompletion_apply]
  by_cases hφ : Extends φ I
  · rw [if_pos hφ]
    symm
    rw [Finset.sum_eq_single (φ x)]
    · rw [if_pos ((extends_addPair_iff I x (φ x) hx
        (unused_of_extends I x hx φ hφ) φ).mpr ⟨hφ, rfl⟩)]
    · intro y hy hne
      apply if_neg
      intro he
      exact hne (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).2.symm)
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unused_of_extends I x hx φ hφ⟩)).elim
  · rw [if_neg hφ]
    symm
    apply Finset.sum_eq_zero
    intro y hy
    apply if_neg
    intro he
    exact hφ (((extends_addPair_iff I x y hx (Finset.mem_filter.mp hy).2 φ).mp he).1)

theorem Hle_succ (r : ℕ) (hr : r < s) : Hle s r ≤ Hle s (r + 1) := by
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, rfl⟩
  obtain ⟨x, hx⟩ := exists_unset I (by omega)
  apply (completion_mem_iff _ I).mpr
  rw [rawCompletion_extension I x hx]
  apply Submodule.sum_mem
  intro y hy
  apply (completion_mem_iff _ _).mp
  apply Submodule.subset_span
  refine ⟨I.addPair x y, ?_, rfl⟩
  rw [size_addPair I x y hx (Finset.mem_filter.mp hy).2, hI]

theorem Hle_mono {r t : ℕ} (hrt : r ≤ t) (ht : t ≤ s) : Hle s r ≤ Hle s t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrt
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (by simpa [Nat.add_assoc] using
      (Hle_succ (s := s) (r + d) (by omega)))

theorem Hle_eq_bot {r : ℕ} (hr : s < r) : Hle s r = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨I, hI, _⟩
  have := size_le I
  omega

theorem Hlevel_le (r : ℕ) : Hlevel s r ≤ Hle s r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact inf_le_left

theorem Hlevel_pairwise_orthogonal (r t : ℕ) (hrt : r ≠ t)
    (u v : Hil (Equiv.Perm (Fin s))) (hu : u ∈ Hlevel s r) (hv : v ∈ Hlevel s t) :
    inner ℂ u v = 0 := by
  have hlt : ∀ {a b : ℕ}, a < b → ∀ x ∈ Hlevel s a, ∀ y ∈ Hlevel s b,
      inner ℂ x y = 0 := by
    intro a b hab x hx y hy
    by_cases hb : b ≤ s
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      have hx' : x ∈ Hle s b := Hle_mono (by omega) (by omega) (Hlevel_le a hx)
      exact ((Hle s b).mem_orthogonal y).mp hy.2 x hx'
    · have hy' : y ∈ (⊥ : Submodule ℂ (Hil (Equiv.Perm (Fin s)))) := by
        simpa only [Hle_eq_bot (by omega : s < b)] using Hlevel_le b hy
      have : y = 0 := hy'
      simp [this]
  rcases lt_or_gt_of_ne hrt with h | h
  · exact hlt h u hu v hv
  · rw [← inner_conj_symm, hlt h v hv u hu]
    simp

end WeldedPath.CompletionLevels

end

-- Solutions.WeldedPathIntertwinerPartial
section

namespace WeldedPath.IntertwinerPartial

open Classical OperatorPolar HilbertSupport
open scoped BigOperators

lemma Gam_range (s r : ℕ) (ψ : Hil (InjDb s)) : Gam s r ψ ∈ Hlevel s r := by
  unfold Gam
  simp only [ContinuousLinearMap.sum_apply, ketBra_apply]
  apply Submodule.sum_mem
  intro I hI
  exact Submodule.smul_mem _ _ ((Hlevel s r).starProjection_apply_mem (completion I))

lemma Gam_ket (s r : ℕ) (I : InjDb s) :
    Gam s r (ket I) = if I.size = r then projLevel s r (completion I) else 0 := by
  simp [Gam, ketBra_apply, inner_ket, ket_apply]

lemma Gam_adjoint_support (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s)))
    (I : InjDb s) (hI : I.size ≠ r) : ContinuousLinearMap.adjoint (Gam s r) ψ I = 0 := by
  rw [← inner_ket I, ContinuousLinearMap.adjoint_inner_right, Gam_ket,
    if_neg hI, inner_zero_left]

lemma Gam_comp_adjoint_zero (s r t : ℕ) (hrt : r ≠ t) :
    (Gam s r).comp (ContinuousLinearMap.adjoint (Gam s t)) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  change Gam s r (ContinuousLinearMap.adjoint (Gam s t) ψ) = 0
  rw [← sum_basis (ContinuousLinearMap.adjoint (Gam s t) ψ)]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro I _
  by_cases hI : I.size = r
  · rw [Gam_adjoint_support s t ψ I (by omega), zero_smul]
  · rw [Gam_ket, if_neg hI, smul_zero]

lemma GramInvSqrt_eq (s r : ℕ) : GramInvSqrt s r = invSqrt (Gram s r) := rfl

lemma Gram_selfadjoint (s r : ℕ) : IsSelfAdjoint (Gram s r) := gram_selfadjoint (Gam s r)

lemma GramInvSqrt_range (s r : ℕ) (ψ : Hil (Equiv.Perm (Fin s))) :
    GramInvSqrt s r ψ ∈ Hlevel s r :=
  invSqrt_mapsTo _ (Gram_selfadjoint s r) (Hlevel s r)
    (fun v => Gam_range s r (ContinuousLinearMap.adjoint (Gam s r) v)) ψ

lemma GramInvSqrt_adjoint (s r : ℕ) :
    ContinuousLinearMap.adjoint (GramInvSqrt s r) = GramInvSqrt s r :=
  invSqrt_adjoint _

lemma GramInvSqrt_comp_zero (s r t : ℕ) (hrt : r ≠ t) :
    (GramInvSqrt s r).comp (GramInvSqrt s t) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_left ℂ
  intro η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, inner_zero_right]
  have he := ContinuousLinearMap.adjoint_inner_right (GramInvSqrt s r) η
    (GramInvSqrt s t ψ)
  rw [GramInvSqrt_adjoint] at he
  rw [he]
  exact CompletionLevels.Hlevel_pairwise_orthogonal r t hrt _ _
    (GramInvSqrt_range s r η) (GramInvSqrt_range s t ψ)

lemma polar_Gam_cross_final (s r t : ℕ) (hrt : r ≠ t) :
    (polarMap (Gam s r)).comp (ContinuousLinearMap.adjoint (polarMap (Gam s t))) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((ContinuousLinearMap.adjoint (Gam s r)).comp (GramInvSqrt s r)).comp
    ((GramInvSqrt s t).comp (Gam s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (GramInvSqrt s r) (GramInvSqrt s t) (Gam s t), GramInvSqrt_comp_zero s r t hrt]
  simp

lemma polar_Gam_cross_initial (s r t : ℕ) (hrt : r ≠ t) :
    (ContinuousLinearMap.adjoint (polarMap (Gam s r))).comp (polarMap (Gam s t)) = 0 := by
  simp only [polarMap, ContinuousLinearMap.adjoint_comp, invSqrt_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  change ((GramInvSqrt s r).comp (Gam s r)).comp
    ((ContinuousLinearMap.adjoint (Gam s t)).comp (GramInvSqrt s t)) = 0
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (Gam s r) (ContinuousLinearMap.adjoint (Gam s t)) (GramInvSqrt s t),
    Gam_comp_adjoint_zero s r t hrt]
  simp

theorem sum_partial {X Y ι : Type*} [Fintype X] [Fintype Y]
    (S : Finset ι) (V : ι → Hil X →L[ℂ] Hil Y)
    (hp : ∀ i ∈ S, ((V i).comp (ContinuousLinearMap.adjoint (V i))).comp (V i) = V i)
    (hf : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (V i).comp (ContinuousLinearMap.adjoint (V j)) = 0)
    (hi : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (ContinuousLinearMap.adjoint (V i)).comp (V j) = 0) :
    (((∑ i ∈ S, V i).comp (ContinuousLinearMap.adjoint (∑ i ∈ S, V i))).comp
      (∑ i ∈ S, V i)) = ∑ i ∈ S, V i := by
  classical
  simp only [map_sum, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i hiS
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · exact hp i hiS
    · intro j hj hji
      rw [hf j hj i hiS hji]
      simp
    · exact fun h => (h hiS).elim
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro k hk
    rw [ContinuousLinearMap.comp_assoc, hi j hj i hiS hji]
    simp
  · exact fun h => (h hiS).elim

theorem intertwiner_partial (s : ℕ) :
    ((intertwiner s).comp (ContinuousLinearMap.adjoint (intertwiner s))).comp
      (intertwiner s) = intertwiner s := by
  change (((∑ r ∈ Finset.range s, polarMap (Gam s r)).comp
    (ContinuousLinearMap.adjoint (∑ r ∈ Finset.range s, polarMap (Gam s r)))).comp
      (∑ r ∈ Finset.range s, polarMap (Gam s r))) =
        ∑ r ∈ Finset.range s, polarMap (Gam s r)
  exact sum_partial _ _ (fun r _ => polarMap_partial (Gam s r))
    (fun r _ t _ hrt => polar_Gam_cross_final s r t hrt)
    (fun r _ t _ hrt => polar_Gam_cross_initial s r t hrt)

end WeldedPath.IntertwinerPartial

end

-- Solutions.WeldedPathPartialIsometryContraction
section

namespace WeldedPath.PartialIsometryContraction

open ContinuousLinearMap

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The exact-oracle block construction is contractive for every partial
isometry and every two contractive constituent maps. -/
theorem block_norm_le (V : Hil X →L[ℂ] Hil Y)
    (hV : (V.comp (adjoint V)).comp V = V)
    (O : Hil X →L[ℂ] Hil X) (C : Hil Y →L[ℂ] Hil Y)
    (hO : ∀ x, ‖O x‖ ≤ ‖x‖) (hC : ∀ y, ‖C y‖ ≤ ‖y‖)
    (ψ : Hil Y) :
    ‖(V.comp (O.comp (adjoint V)) +
      ((1 : Hil Y →L[ℂ] Hil Y) - V.comp (adjoint V)).comp
        (C.comp ((1 : Hil Y →L[ℂ] Hil Y) - V.comp (adjoint V)))) ψ‖ ≤ ‖ψ‖ := by
  let P := V.comp (adjoint V)
  let R : Hil Y →L[ℂ] Hil Y := 1 - P
  have hPv : ∀ x, P (V x) = V x := fun x =>
    congrArg (fun T : Hil X →L[ℂ] Hil Y => T x) hV
  have hPP : ∀ y, P (P y) = P y := fun y => hPv (adjoint V y)
  have hPstar : adjoint P = P := by simp only [P, adjoint_comp, adjoint_adjoint]
  have hP : IsStarProjection P := by
    refine ⟨?_, ?_⟩
    · exact ContinuousLinearMap.ext hPP
    · exact hPstar
  have hR : IsStarProjection R := hP.one_sub
  have hVadj : (adjoint V).comp P = adjoint V := by
    have hh := congrArg adjoint hV
    simpa only [adjoint_comp, adjoint_adjoint, comp_assoc, P] using hh
  have hVR : ∀ y, adjoint V (R y) = 0 := by
    intro y
    have hh := congrArg (fun T : Hil Y →L[ℂ] Hil X => T y) hVadj
    change adjoint V (y - P y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hh.symm
  have horth : ∀ x y, inner ℂ (V x) (R y) = 0 := by
    intro x y
    rw [← adjoint_inner_right, hVR, inner_zero_right]
  have hnV : ‖V‖ ≤ 1 := by
    have hh := IsStarProjection.norm_le P hP
    have he := norm_adjoint_comp_self (adjoint V)
    simp only [adjoint_adjoint, LinearIsometryEquiv.norm_map] at he
    change ‖P‖ = ‖V‖ * ‖V‖ at he
    nlinarith [norm_nonneg V]
  have hVnorm : ∀ x, ‖V x‖ ≤ ‖x‖ := by
    intro x
    exact (le_opNorm V x).trans (by simpa using mul_le_mul_of_nonneg_right hnV (norm_nonneg x))
  have hRnorm : ∀ y, ‖R y‖ ≤ ‖y‖ := by
    intro y
    calc
      ‖R y‖ ≤ ‖R‖ * ‖y‖ := le_opNorm R y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le R hR) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have henergy : ‖P ψ‖ ^ 2 = ‖adjoint V ψ‖ ^ 2 := by
    rw [apply_norm_sq_eq_inner_adjoint_right P,
      apply_norm_sq_eq_inner_adjoint_right (adjoint V), adjoint_adjoint]
    simp only [hPstar, comp_apply]
    change RCLike.re (inner ℂ ψ (P (P ψ))) = RCLike.re (inner ℂ ψ (P ψ))
    rw [hPP]
  have hinput : ‖ψ‖ ^ 2 = ‖adjoint V ψ‖ ^ 2 + ‖R ψ‖ ^ 2 := by
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (P ψ) (R ψ) (horth (adjoint V ψ) ψ)
    have he : P ψ + R ψ = ψ := by change P ψ + (ψ - P ψ) = ψ; abel
    simp only [← sq, he, henergy] at hh
    exact hh
  let a := V (O (adjoint V ψ))
  let b := R (C (R ψ))
  have ha : ‖a‖ ≤ ‖adjoint V ψ‖ := (hVnorm _).trans (hO _)
  have hb : ‖b‖ ≤ ‖R ψ‖ := (hRnorm _).trans (hC _)
  have hout : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b (horth _ _)
  have ha2 := (sq_le_sq₀ (norm_nonneg a) (norm_nonneg (adjoint V ψ))).mpr ha
  have hb2 := (sq_le_sq₀ (norm_nonneg b) (norm_nonneg (R ψ))).mpr hb
  change ‖a + b‖ ≤ ‖ψ‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end WeldedPath.PartialIsometryContraction

end

-- Solutions.WeldedPathExactContraction
section

namespace WeldedPath.ExactContraction

open Classical QAlgorithms Supplement EncodedOracleUnitary CompressedPrimitive
open scoped BigOperators

theorem exactCpOE_norm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) (ψ : Hil (Qubits d × InjDb s)) :
    ‖exactCpOE enc x inv ψ‖ ≤ ‖ψ‖ := by
  exact PartialIsometryContraction.block_norm_le
    (opTensor (1 : Hil (Qubits d) →L[ℂ] Hil (Qubits d)) (intertwiner s))
    (TensorOperators.opTensor_one_partial (intertwiner s)
      (IntertwinerPartial.intertwiner_partial s))
    (stdQueryE enc x inv) (cpOE enc x inv)
    (fun v => (stdQueryE_norm enc x inv v).le) (cpOE_norm_le enc x inv) ψ

theorem exactCpO_norm_le {s : ℕ} (d : ℕ) (x : Fin s) (inv : Bool)
    (ψ : Hil (Qubits d × InjDb s)) : ‖exactCpO d x inv ψ‖ ≤ ‖ψ‖ :=
  exactCpOE_norm_le (encode d) x inv ψ

theorem basisMap_involutive_adjoint {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → X) (hf : Function.Involutive f) :
    ContinuousLinearMap.adjoint (basisMap f) = basisMap f := by
  simp only [basisMap, ketBra_eq_rankOne, map_sum, InnerProductSpace.adjoint_rankOne]
  calc
    _ = ∑ i, InnerProductSpace.rankOne ℂ (ket (f i)) (ket (f (f i))) :=
      (Equiv.sum_comp (hf.toPerm f)
        (fun i => InnerProductSpace.rankOne ℂ (ket i) (ket (f i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hf i]

theorem stdQueryE_adjoint {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (stdQueryE enc x inv) = stdQueryE enc x inv := by
  apply basisMap_involutive_adjoint
  rintro ⟨a, π⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

theorem purifiedXorE_adjoint {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) :
    ContinuousLinearMap.adjoint (purifiedXorE enc x) = purifiedXorE enc x := by
  apply basisMap_involutive_adjoint
  rintro ⟨a, I⟩
  cases h : I x with
  | none => simp only [h]
  | some y => simp only [h, qubits_add_cancel]

theorem cpOE_adjoint {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (cpOE enc x inv) = cpOE enc x inv := by
  cases inv <;> simp only [cpOE, Bool.false_eq_true, if_false, if_true,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    purifiedXorE_adjoint, ContinuousLinearMap.comp_assoc]

theorem exactCpOE_adjoint {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (exactCpOE enc x inv) = exactCpOE enc x inv := by
  simp only [exactCpOE, map_add, map_sub, ContinuousLinearMap.adjoint_one,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    stdQueryE_adjoint, cpOE_adjoint, ContinuousLinearMap.comp_assoc]

theorem exactCpO_adjoint {s : ℕ} (d : ℕ) (x : Fin s) (inv : Bool) :
    ContinuousLinearMap.adjoint (exactCpO d x inv) = exactCpO d x inv :=
  exactCpOE_adjoint (encode d) x inv

theorem exactCpOE_opNorm_le {s d : ℕ} (enc : Fin s → Qubits d)
    (x : Fin s) (inv : Bool) : ‖exactCpOE enc x inv‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using exactCpOE_norm_le enc x inv ψ

theorem controlled_ket {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq X]
    (T : C → Hil X →L[ℂ] Hil Y) (c : C) (x : X) :
    controlled T (ket (c, x)) = ketTensor (ket c) (T c (ket x)) := by
  ext p
  rcases p with ⟨a, y⟩
  rw [ControlledOperators.controlled_apply]
  by_cases ha : a = c
  · subst a
    have hs : slice (ket (c, x)) c = ket x := by
      ext z
      simp [slice, HilbertSupport.ket_apply]
    rw [hs]
    simp [HilbertSupport.ketTensor_apply, HilbertSupport.ket_apply]
  · have hs : slice (ket (c, x)) a = 0 := by
      ext z
      simp [slice, HilbertSupport.ket_apply, ha]
    rw [hs, map_zero]
    simp [HilbertSupport.ketTensor_apply, HilbertSupport.ket_apply, ha]

theorem controlled_adjoint {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (T : C → Hil X →L[ℂ] Hil Y) :
    ContinuousLinearMap.adjoint (controlled T) =
      controlled (fun c => ContinuousLinearMap.adjoint (T c)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  ext p
  rcases p with ⟨c, x⟩
  rw [← HilbertSupport.inner_ket (c, x), ContinuousLinearMap.adjoint_inner_right,
    controlled_ket, TensorOperators.inner_ketTensor_slice,
    ← ContinuousLinearMap.adjoint_inner_right, HilbertSupport.inner_ket,
    ControlledOperators.controlled_apply]

theorem controlled_exactCpOE_adjoint {C : Type*} [Fintype C] [DecidableEq C]
    {s d : ℕ} (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool) :
    ContinuousLinearMap.adjoint (controlled (fun c => exactCpOE (enc c) (x c) (inv c))) =
      controlled (fun c => exactCpOE (enc c) (x c) (inv c)) := by
  rw [controlled_adjoint]
  simp only [exactCpOE_adjoint]

theorem controlled_exactCpOE_opNorm_le {C : Type*} [Fintype C] [DecidableEq C]
    {s d : ℕ} (enc : C → Fin s → Qubits d) (x : C → Fin s) (inv : C → Bool) :
    ‖controlled (fun c => exactCpOE (enc c) (x c) (inv c))‖ ≤ 1 :=
  ControlledOperators.controlled_opNorm_le _
    (fun c ψ => exactCpOE_norm_le (enc c) (x c) (inv c) ψ)

end WeldedPath.ExactContraction

end

-- Solutions.WeldedPathLabelRegisterContraction
section

namespace WeldedPath.LabelRegisterContraction

open Classical QAlgorithms Supplement EncodedOracleUnitary ExactContraction RegisterTransport

variable {n : ℕ}

abbrev Bits (n : ℕ) := Qubits (2 * n + 1)
abbrev InvControl (l : ℕ) (G : WeldedInstance n) := QReg n × (EdgeDb l G × Bits n)

noncomputable def invEquiv (l : ℕ) (G : WeldedInstance n) :
    FullReg l G ≃ InvControl l G × (Bits n × LabelDb n) where
  toFun p := ((p.1.1, (p.1.2.2, p.2.2)), (p.2.1, p.1.2.1))
  invFun p := ((p.1.1, (p.2.2, p.1.2.1)), (p.2.1, p.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def invOp (l : ℕ) (G : WeldedInstance n) (c : InvControl l G) :
    Hil (Bits n × LabelDb n) →L[ℂ] Hil (Bits n × LabelDb n) :=
  match toIdx n (bitsToNat c.1.1.1) with
  | some x => exactCpOE (encLabel n) x true
  | none => 1

theorem invOp_norm_le (l : ℕ) (G : WeldedInstance n) (c : InvControl l G)
    (ψ : Hil (Bits n × LabelDb n)) : ‖invOp l G c ψ‖ ≤ ‖ψ‖ := by
  unfold invOp
  cases toIdx n (bitsToNat c.1.1.1) with
  | none => exact le_rfl
  | some x => exact exactCpOE_norm_le (encLabel n) x true ψ

theorem stepInvLab_norm_le (l : ℕ) (G : WeldedInstance n) (ψ : Hil (FullReg l G)) :
    ‖stepInvLab l G ψ‖ ≤ ‖ψ‖ := by
  have he : stepInvLab l G = ofBasis (fun p =>
      partImg (invOp l G ((invEquiv l G) p).1) ((invEquiv l G) p).2
        (fun x => (invEquiv l G).symm (((invEquiv l G) p).1, x))) := by
    unfold stepInvLab
    congr 1
    funext p
    dsimp only [invEquiv, invOp, Equiv.coe_fn_mk, Equiv.symm_mk]
    cases h : toIdx n (bitsToNat p.1.1.1.1) with
    | none => simp [h, partImg_one]
    | some x => rfl
  rw [he]
  exact ofBasis_partImg_norm_le (invEquiv l G) (invOp l G) (invOp_norm_le l G) ψ

abbrev ForControl (l : ℕ) (G : WeldedInstance n) :=
  (Bits n × Fin 3) × (EdgeDb l G × ZReg n)

noncomputable def forEquiv (l : ℕ) (G : WeldedInstance n) :
    FullReg l G ≃ ForControl l G × (Bits n × LabelDb n) where
  toFun p := ((p.1.1.1, (p.1.2.2, p.2)), (p.1.1.2, p.1.2.1))
  invFun p := (((p.1.1, p.2.1), (p.2.2, p.1.2.1)), p.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def xorLabel (x : ℕ) :
    Hil (Bits n × LabelDb n) →L[ℂ] Hil (Bits n × LabelDb n) :=
  basisMap fun p => (p.1 + natToBits (2 * n + 1) x, p.2)

theorem xorLabel_norm (x : ℕ) (ψ : Hil (Bits n × LabelDb n)) :
    ‖xorLabel x ψ‖ = ‖ψ‖ := by
  apply basisMap_involutive_norm
  rintro ⟨a, I⟩
  exact Prod.ext (qubits_add_cancel a _) rfl

noncomputable def forOp (l : ℕ) (G : WeldedInstance n) (c : ForControl l G) :
    Hil (Bits n × LabelDb n) →L[ℂ] Hil (Bits n × LabelDb n) :=
  let x := bitsToNat c.1.1
  let v := bitsToNat c.2.2.1
  if x ≠ 0 ∧ v = 0 then 1
  else match wOf l G v c.1.2 (bitsToNat c.2.2.2) with
  | none => 1
  | some w =>
    if w = v then xorLabel x
    else if w = 0 then 1
    else match toIdx n w with
    | none => 1
    | some i => exactCpOE (encLabel n) i false

theorem forOp_norm_le (l : ℕ) (G : WeldedInstance n) (c : ForControl l G)
    (ψ : Hil (Bits n × LabelDb n)) : ‖forOp l G c ψ‖ ≤ ‖ψ‖ := by
  unfold forOp
  dsimp only
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · split
      · exact (xorLabel_norm _ ψ).le
      · split
        · exact le_rfl
        · split
          · exact le_rfl
          · exact exactCpOE_norm_le _ _ _ ψ

theorem stepForLab_norm_le (l : ℕ) (G : WeldedInstance n) (ψ : Hil (FullReg l G)) :
    ‖stepForLab l G ψ‖ ≤ ‖ψ‖ := by
  have he : stepForLab l G = ofBasis (fun p =>
      partImg (forOp l G ((forEquiv l G) p).1) ((forEquiv l G) p).2
        (fun x => (forEquiv l G).symm (((forEquiv l G) p).1, x))) := by
    unfold stepForLab
    congr 1
    funext p
    dsimp only [forEquiv, forOp, Equiv.coe_fn_mk, Equiv.symm_mk]
    by_cases hskip : bitsToNat p.1.1.1.1 ≠ 0 ∧ bitsToNat p.2.1 = 0
    · simp [hskip, partImg_one]
    · simp only [hskip, if_false]
      cases hw : wOf l G (bitsToNat p.2.1) p.1.1.1.2 (bitsToNat p.2.2) with
      | none => simp [partImg_one]
      | some w =>
        by_cases heq : w = bitsToNat p.2.1
        · simp [heq, xorLabel, partImg_basisMap]
        · simp only [heq, if_false]
          by_cases hz : w = 0
          · simp [hz, partImg_one]
          · simp only [hz, if_false]
            cases hi : toIdx n w with
            | none => simp [partImg_one]
            | some i => rfl
  rw [he]
  exact ofBasis_partImg_norm_le (forEquiv l G) (forOp l G) (forOp_norm_le l G) ψ

end WeldedPath.LabelRegisterContraction

end

-- Solutions.WeldedPathEdgeRegisterContraction
section

namespace WeldedPath.EdgeRegisterContraction

open Classical QAlgorithms Supplement ExactContraction RegisterTransport HilbertSupport
open scoped BigOperators

variable {n : ℕ}

abbrev Bits (n : ℕ) := Qubits (2 * n + 1)
abbrev RestDb (l : ℕ) (G : WeldedInstance n) (b : PClass n l) :=
  (c : {c : PClass n l // c ≠ b}) → InjDb (classSize l G c.val)

noncomputable def edgeSplit (l : ℕ) (G : WeldedInstance n) (b : PClass n l) :
    (Bits n × EdgeDb l G) ≃ RestDb l G b × (Bits n × InjDb (classSize l G b)) :=
  ((Equiv.prodCongr (Equiv.refl (Bits n))
    (Equiv.piSplitAt b (fun c => InjDb (classSize l G c)))).trans
      (Equiv.prodAssoc (Bits n) (InjDb (classSize l G b)) (RestDb l G b)).symm).trans
    (Equiv.prodComm _ _)

lemma edgeSplit_snd (l : ℕ) (G : WeldedInstance n) (b : PClass n l)
    (p : Bits n × EdgeDb l G) : (edgeSplit l G b p).2 = (p.1, p.2 b) := rfl

lemma edgeSplit_put (l : ℕ) (G : WeldedInstance n) (b : PClass n l)
    (p : Bits n × EdgeDb l G) (q : Bits n × InjDb (classSize l G b)) :
    (edgeSplit l G b).symm ((edgeSplit l G b p).1, q) =
      (q.1, Function.update p.2 b q.2) := by
  apply Prod.ext rfl
  funext c
  by_cases hc : c = b
  · subst c
    simp [edgeSplit, Equiv.piSplitAt]
  · simp [edgeSplit, Equiv.piSplitAt, hc]

noncomputable def edgeAction (l : ℕ) (G : WeldedInstance n) (b : PClass n l)
    (T : Hil (Bits n × InjDb (classSize l G b)) →L[ℂ]
      Hil (Bits n × InjDb (classSize l G b))) :
    Hil (Bits n × EdgeDb l G) →L[ℂ] Hil (Bits n × EdgeDb l G) :=
  ofBasis fun p => partImg T (p.1, p.2 b) (fun q => (q.1, Function.update p.2 b q.2))

theorem edgeAction_norm_le (l : ℕ) (G : WeldedInstance n) (b : PClass n l)
    (T : Hil (Bits n × InjDb (classSize l G b)) →L[ℂ]
      Hil (Bits n × InjDb (classSize l G b)))
    (hT : ∀ ψ, ‖T ψ‖ ≤ ‖ψ‖) (ψ : Hil (Bits n × EdgeDb l G)) :
    ‖edgeAction l G b T ψ‖ ≤ ‖ψ‖ := by
  have he : edgeAction l G b T = ofBasis (fun p =>
      partImg T ((edgeSplit l G b) p).2
        (fun q => (edgeSplit l G b).symm (((edgeSplit l G b) p).1, q))) := by
    unfold edgeAction
    congr 1
  rw [he]
  exact ofBasis_partImg_norm_le (edgeSplit l G b) (fun _ => T) (fun _ => hT) ψ

lemma partImg_eq_basisMap {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (T : Hil X →L[ℂ] Hil X) (x : X) (put : X → Y) :
    partImg T x put = basisMap put (T (ket x)) := by
  conv_rhs => rw [← sum_basis (T (ket x))]
  simp only [partImg, inner_ket, map_sum, map_smul, basisMap_ket]

lemma basisMap_partImg {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Hil X →L[ℂ] Hil X) (x : X) (put : X → Y) (f : Y → Z) :
    basisMap f (partImg T x put) = partImg T x (fun y => f (put y)) := by
  simp only [partImg, map_sum, map_smul, basisMap_ket]

lemma partImg_edgeAction {Y : Type*} [Fintype Y] [DecidableEq Y]
    (l : ℕ) (G : WeldedInstance n) (b : PClass n l)
    (T : Hil (Bits n × InjDb (classSize l G b)) →L[ℂ]
      Hil (Bits n × InjDb (classSize l G b)))
    (p : Bits n × EdgeDb l G) (put : (Bits n × EdgeDb l G) → Y) :
    partImg (edgeAction l G b T) p put =
      partImg T (p.1, p.2 b) (fun q => put (q.1, Function.update p.2 b q.2)) := by
  rw [partImg_eq_basisMap]
  unfold edgeAction
  rw [ofBasis_ket, basisMap_partImg]

abbrev EdgeControl (n : ℕ) := (QReg n × LabelDb n) × Bits n

noncomputable def edgeEquiv (l : ℕ) (G : WeldedInstance n) :
    FullReg l G ≃ EdgeControl n × (Bits n × EdgeDb l G) where
  toFun p := (((p.1.1, p.1.2.1), p.2.1), (p.2.2, p.1.2.2))
  invFun p := ((p.1.1.1, (p.1.1.2, p.2.2)), (p.1.2, p.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def edgeOp (l : ℕ) (G : WeldedInstance n) (c : EdgeControl n) :
    Hil (Bits n × EdgeDb l G) →L[ℂ] Hil (Bits n × EdgeDb l G) :=
  let x := bitsToNat c.1.1.1.1
  let v := bitsToNat c.2
  if x ≠ 0 ∧ v = 0 then 1
  else match permData l G v c.1.1.1.2 with
  | some ⟨b, e, isTail⟩ => edgeAction l G b
      (exactCpOE (encEdge n (classSize l G b)) (edgeIdx l G b e) (!isTail))
  | none => 1

theorem edgeOp_norm_le (l : ℕ) (G : WeldedInstance n) (c : EdgeControl n)
    (ψ : Hil (Bits n × EdgeDb l G)) : ‖edgeOp l G c ψ‖ ≤ ‖ψ‖ := by
  unfold edgeOp
  dsimp only
  split
  · exact le_rfl
  · split
    · exact edgeAction_norm_le l G _ _ (exactCpOE_norm_le _ _ _) ψ
    · exact le_rfl

theorem stepEdge_norm_le (l : ℕ) (G : WeldedInstance n) (ψ : Hil (FullReg l G)) :
    ‖stepEdge l G ψ‖ ≤ ‖ψ‖ := by
  have he : stepEdge l G = ofBasis (fun p =>
      partImg (edgeOp l G ((edgeEquiv l G) p).1) ((edgeEquiv l G) p).2
        (fun x => (edgeEquiv l G).symm (((edgeEquiv l G) p).1, x))) := by
    unfold stepEdge
    congr 1
    funext p
    dsimp only [edgeEquiv, edgeOp, Equiv.coe_fn_mk, Equiv.symm_mk]
    by_cases hskip : bitsToNat p.1.1.1.1 ≠ 0 ∧ bitsToNat p.2.1 = 0
    · simp [hskip, partImg_one]
    · simp only [hskip, if_false]
      cases hp : permData l G (bitsToNat p.2.1) p.1.1.1.2 with
      | none => simp [partImg_one]
      | some d =>
        rcases d with ⟨b, e, isTail⟩
        rw [partImg_edgeAction]
  rw [he]
  exact ofBasis_partImg_norm_le (edgeEquiv l G) (edgeOp l G) (edgeOp_norm_le l G) ψ

end WeldedPath.EdgeRegisterContraction

end

-- Solutions.WeldedPathZeroRegisterIsometry
section

namespace WeldedPath.ZeroRegisterIsometry

open Classical QAlgorithms Supplement HilbertSupport RegisterTransport
open scoped BigOperators

variable {n : ℕ}

theorem isoZ_apply (l : ℕ) (G : WeldedInstance n)
    (ψ : Hil (QReg n × Db l G)) (p : QReg n × Db l G) (z : ZReg n) :
    isoZ l G ψ (p, z) = if z = (0, 0) then ψ p else 0 := by
  by_cases hz : z = (0, 0) <;>
    simp [isoZ, ofBasis, ketBra_apply, inner_ket, ket_apply, Prod.mk.injEq, hz]

theorem isoZ_norm (l : ℕ) (G : WeldedInstance n) (ψ : Hil (QReg n × Db l G)) :
    ‖isoZ l G ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ = ∑ p : QReg n × Db l G, ∑ z : ZReg n, ‖isoZ l G ψ (p, z)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    _ = ∑ p : QReg n × Db l G, ‖ψ p‖ ^ 2 := by simp [isoZ_apply, apply_ite]
    _ = _ := (EuclideanSpace.norm_sq_eq ψ).symm

theorem isoZ_adjoint_norm_le (l : ℕ) (G : WeldedInstance n)
    (ψ : Hil (FullReg l G)) : ‖ContinuousLinearMap.adjoint (isoZ l G) ψ‖ ≤ ‖ψ‖ := by
  have hnorm : ‖isoZ l G‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro φ
    simp only [isoZ_norm, one_mul, le_refl]
  have hadj : ‖ContinuousLinearMap.adjoint (isoZ l G)‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hnorm
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint (isoZ l G)‖ * ‖ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right hadj (norm_nonneg _)
    _ = ‖ψ‖ := one_mul _

end WeldedPath.ZeroRegisterIsometry

end

-- Solutions.WeldedPathWeldedContraction
section

namespace WeldedPath.WeldedContraction

open Classical QAlgorithms Supplement HilbertSupport
open LabelRegisterContraction EdgeRegisterContraction ZeroRegisterIsometry QueryRunContraction

variable {n : ℕ}

theorem exactCpWTCirc_norm_le (l : ℕ) (G : WeldedInstance n) (ψ : Hil (FullReg l G)) :
    ‖exactCpWTCirc l G ψ‖ ≤ ‖ψ‖ := by
  unfold exactCpWTCirc
  simp only [ContinuousLinearMap.comp_apply]
  exact (stepInvLab_norm_le l G _).trans ((stepEdge_norm_le l G _).trans
    ((stepForLab_norm_le l G _).trans ((stepEdge_norm_le l G _).trans
      (stepInvLab_norm_le l G ψ))))

theorem exactCpWT_norm_le (l : ℕ) (G : WeldedInstance n) (ψ : Hil (QReg n × Db l G)) :
    ‖exactCpWT l G ψ‖ ≤ ‖ψ‖ := by
  unfold exactCpWT
  simp only [ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ‖exactCpWTCirc l G (isoZ l G ψ)‖ := isoZ_adjoint_norm_le l G _
    _ ≤ ‖isoZ l G ψ‖ := exactCpWTCirc_norm_le l G _
    _ = ‖ψ‖ := isoZ_norm l G ψ

theorem exactCpWT_opNorm_le (l : ℕ) (G : WeldedInstance n) : ‖exactCpWT l G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simpa only [one_mul] using exactCpWT_norm_le l G ψ

theorem pCross_mem_unitInterval (l : ℕ) (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (alg : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q) :
    0 ≤ pCross l G alg ∧ pCross l G alg ≤ 1 := by
  constructor
  · exact sq_nonneg _
  · have hstate := finalStateDb_norm_le alg (exactCpWT l G) (exactCpWT_norm_le l G) (emptyDb l G)
    have hproj := diagProj_norm_le
      (fun p : (QReg n × W) × Db l G => HasCrossing l G p.2.2)
      (finalStateDb alg (exactCpWT l G) (emptyDb l G))
    have hnorm : ‖projCross l G W (finalStateDb alg (exactCpWT l G) (emptyDb l G))‖ ≤ 1 :=
      hproj.trans hstate
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hnorm |>.trans_eq (by norm_num)

end WeldedPath.WeldedContraction

end

-- Solutions.WeldedPathCrossingReduction
section

namespace WeldedPath.CrossingReduction

open Classical QAlgorithms Supplement HilbertSupport RunProjection
open QueryRunContraction WeldedContraction LeakageTelescoping CrossingScalar

variable {n : ℕ}

set_option maxHeartbeats 1200000

theorem complement_projection_norm_le {X : Type*} [Fintype X]
    (K : Submodule ℂ (Hil X)) (ψ : Hil X) :
    ‖(1 - K.starProjection) ψ‖ ≤ ‖ψ‖ := by
  change ‖(ContinuousLinearMap.id ℂ (Hil X) - K.starProjection) ψ‖ ≤ ‖ψ‖
  rw [← K.starProjection_orthogonal]
  exact Kᗮ.norm_starProjection_apply_le ψ

/-- The actual query-algorithm crossing probability follows from the canonical
single-query good-space estimate. The latter is the only analytic hypothesis. -/
theorem pCross_of_local_leakage (l : ℕ) (G : WeldedInstance n)
    (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ} (hq : 1 ≤ q)
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (C : ℝ) (hC : 0 ≤ C)
    (hleak : ∀ (i : Fin q) (ψ : Hil (QReg n × Db l G)),
      ‖(1 - projGood l G (6 * i.val + 6))
          (exactCpWT l G (projGood l G (6 * i.val) ψ))‖ ≤
        C * etaStep n l (6 * i.val) * ‖ψ‖) :
    pCross l G A ≤ 7 * C ^ 2 * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
      (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  let P : Fin (q + 1) → Hil ((QReg n × W) × Db l G) →L[ℂ]
      Hil ((QReg n × W) × Db l G) := fun i =>
    opTensor 1 (goodSpace l G (Vbd n l) (6 * i.val)).starProjection
  have hPlift (i : Fin (q + 1)) :
      P i = liftOracle (W := W) (projGood l G (6 * i.val)) := by
    exact (liftOracle_dbOp _).symm
  apply crossing_of_local_leakage n l q hq C hC
    (stateAtDb A (exactCpWT l G) (emptyDb l G)) P
    (fun i => liftAlgU (A.U i.succ : Matrix _ _ ℂ))
    (liftOracle (exactCpWT l G)) (projCross l G W)
  · exact liftOracle_norm_le _ (exactCpWT_norm_le l G)
  · intro i ψ
    exact liftAlgU_norm_le _ (A.U i.succ).property ψ
  · intro i ψ
    change ‖(1 - opTensor (1 : Hil (QReg n × W) →L[ℂ] Hil (QReg n × W))
        (goodSpace l G (Vbd n l) (6 * i.val)).starProjection) ψ‖ ≤ _
    rw [opTensor_one_sub]
    exact opTensor_one_norm_le _ (complement_projection_norm_le _) ψ
  · intro i
    exact dbOp_commutes_liftAlgU _ _
  · intro i
    exact Fin.induction_succ _ _ i
  · exact stateAtDb_norm_le A _ (exactCpWT_norm_le l G) (emptyDb l G)
  · change P 0 (liftAlgU (A.U 0 : Matrix _ _ ℂ)
        (ketTensor A.start (ket (emptyDb l G)))) = _
    have hc := congrArg (fun T : Hil ((QReg n × W) × Db l G) →L[ℂ]
        Hil ((QReg n × W) × Db l G) => T (ketTensor A.start (ket (emptyDb l G))))
      (dbOp_commutes_liftAlgU (A.U 0 : Matrix _ _ ℂ)
        (goodSpace l G (Vbd n l) (6 * (0 : Fin (q + 1)).val)).starProjection)
    change P 0 (liftAlgU (A.U 0 : Matrix _ _ ℂ)
        (ketTensor A.start (ket (emptyDb l G)))) =
      liftAlgU (A.U 0 : Matrix _ _ ℂ)
        (P 0 (ketTensor A.start (ket (emptyDb l G)))) at hc
    calc
      _ = liftAlgU (A.U 0 : Matrix _ _ ℂ)
          (P 0 (ketTensor A.start (ket (emptyDb l G)))) := hc
      _ = _ := ?_
    congr 1
    change opTensor 1 _ (ketTensor _ _) = _
    rw [opTensor_one_ketTensor, GoodEmpty.good_starProjection_empty]
  · intro i ψ
    rw [hPlift i.succ, hPlift i.castSucc, liftOracle_one_sub]
    have ht : 6 * i.succ.val = 6 * i.val + 6 := by simp [Nat.mul_add]
    have hb := BoundedControl.liftOracle_norm_bound
      ((1 - projGood l G (6 * i.val + 6)).comp
        ((exactCpWT l G).comp (projGood l G (6 * i.val))))
      (C * etaStep n l (6 * i.val)) (mul_nonneg hC (Real.sqrt_nonneg _))
      (hleak i) ψ
    rw [← liftOracle_comp, ← liftOracle_comp] at hb
    simpa only [ContinuousLinearMap.comp_apply, ht, Fin.val_castSucc,
      etaStep, stepError] using hb
  · exact diagProj_norm_le _
  · apply ContinuousLinearMap.ext
    intro ψ
    letI : DecidableEq ((QReg n × W) × Db l G) := Classical.decEq _
    change diagProj (fun p : (QReg n × W) × Db l G => HasCrossing l G p.2.2)
      (P (Fin.last q) ψ) = 0
    apply (diagProj_zero_iff _ _).mpr
    rintro ⟨a, I⟩ hI
    change opTensor (1 : Hil (QReg n × W) →L[ℂ] Hil (QReg n × W))
      (goodSpace l G (Vbd n l) (6 * q)).starProjection ψ (a, I) = 0
    rw [EncodedOracleUnitary.opTensor_one_apply]
    exact CrossingSupport.goodSpace_coordinate_zero hG hl hln (6 * q) _
      ((goodSpace l G (Vbd n l) (6 * q)).starProjection_apply_mem _) I hI

end WeldedPath.CrossingReduction

end

open Classical WeldedPath WeldedPath.Supplement QAlgorithms

namespace CrossingSketch

theorem reduction (hgood :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp
          ((exactCpWT l G).comp (projGood l G t))‖ ≤
        C * etaStep n l t) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q,
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      pCross l G A ≤ C * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
        (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, K, hK, hlocal⟩ := hgood
  refine ⟨C₀, hC₀, 7 * K ^ 2, by positivity, ?_⟩
  intro n l heven hn hl hln G hG W _ _ q hq A hfirst hsmall
  apply CrossingReduction.pCross_of_local_leakage l G hG (by omega) (by omega)
    hq A K (le_of_lt hK)
  intro i ψ
  have ht : 6 * i.val ≤ 6 * q := Nat.mul_le_mul_left 6 (Nat.le_of_lt i.isLt)
  have hb := hlocal n l heven hn hl hln G hG q (6 * i.val) ht hfirst hsmall
  calc
    _ ≤ ‖(1 - projGood l G (6 * i.val + 6)).comp
        ((exactCpWT l G).comp (projGood l G (6 * i.val)))‖ * ‖ψ‖ :=
      ContinuousLinearMap.le_opNorm _ ψ
    _ ≤ K * etaStep n l (6 * i.val) * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)

end CrossingSketch

theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q,
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      pCross l G A ≤ C * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
        (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by
  exact CrossingSketch.reduction WeldedPath.Supplement.exact_query_goodness
