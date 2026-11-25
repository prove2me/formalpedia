-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.quad_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:49.188293+00:00
-- url     : https://prove2.me/submissions/3b812fbf-2ada-43f9-87f9-4f479a02cdf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
section quad
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
private theorem norm_iteratedFDeriv_le_of_fderiv_eq_quadratic
    (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  rcases a with _ | a
  · refine ⟨1, zero_le_one, fun z _ => ?_⟩
    rw [norm_iteratedFDeriv_zero, one_mul, zero_add, pow_one]
    exact le_max_right _ _
  · choose! K hK0 hK using ih
    refine ⟨‖Bi‖ * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * (K i * K (a - i)),
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i hi => ?_), fun z hz => ?_⟩
    · have hi' := Finset.mem_range.1 hi
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (hK0 (a - i) (by omega)))
    · have hm : 1 ≤ max 1 ‖φ z‖ := le_max_left _ _
      have hm0 : 0 ≤ max 1 ‖φ z‖ := zero_le_one.trans hm
      have heq : Set.EqOn (fderiv ℝ φ) (fun y => Bi (φ y) (φ y)) U := fun y hy => hd y hy
      have e1 : ‖iteratedFDeriv ℝ (a + 1) φ z‖ =
          ‖iteratedFDerivWithin ℝ a (fun y => Bi (φ y) (φ y)) U z‖ := by
        rw [← norm_iteratedFDeriv_fderiv,
          ← (iteratedFDerivWithin_of_isOpen a hU hz :
            iteratedFDerivWithin ℝ a (fderiv ℝ φ) U z = iteratedFDeriv ℝ a (fderiv ℝ φ) z),
          iteratedFDerivWithin_congr heq hz]
      rw [e1]
      refine (Bi.norm_iteratedFDerivWithin_le_of_bilinear (hφ a) (hφ a) hU.uniqueDiffOn hz
        le_rfl).trans ?_
      rw [mul_assoc ‖Bi‖, Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg _)
      have hi' := Finset.mem_range.1 hi
      rw [iteratedFDerivWithin_of_isOpen i hU hz, iteratedFDerivWithin_of_isOpen (a - i) hU hz]
      have h1 := hK i (by omega) z hz
      have h2 := hK (a - i) (by omega) z hz
      have hpow : max 1 ‖φ z‖ ^ (a + 1 + 1) =
          max 1 ‖φ z‖ ^ (i + 1) * max 1 ‖φ z‖ ^ (a - i + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ z‖ * ‖iteratedFDeriv ℝ (a - i) φ z‖
          ≤ (a.choose i : ℝ) * (K i * max 1 ‖φ z‖ ^ (i + 1)) *
              (K (a - i) * max 1 ‖φ z‖ ^ (a - i + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
            exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (pow_nonneg hm0 _))
        _ = (a.choose i : ℝ) * (K i * K (a - i)) * max 1 ‖φ z‖ ^ (a + 1 + 1) := by
            rw [hpow]; ring
end quad
section words
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
end words
end PI.UnitaryGroupMassFormula.UsCost.ZI
end
end

set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ∀ a ≤ n, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  choose K hK0 hK using norm_iteratedFDeriv_le_of_fderiv_eq_quadratic Bi hU hφ hd
  refine ⟨∑ a ∈ Finset.range (n + 1), K a, Finset.sum_nonneg fun a _ => hK0 a,
    fun z hz a ha => ?_⟩
  refine (hK a z hz).trans (mul_le_mul_of_nonneg_right ?_
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  exact Finset.single_le_sum (f := K) (fun b _ => hK0 b) (Finset.mem_range.2 (by omega))
end PI.UnitaryGroupMassFormula.UsCost.ZI
