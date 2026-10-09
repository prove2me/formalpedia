-- Prove2me | solution 1 for WeilDefect.MarkerStability.marker_lower_iff_scaled_covariance_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T14:10:11.634611+00:00
-- url     : https://prove2.me/submissions/083addf0-8c2b-4d83-9f01-336fc312890a

import Theorems.Thm_WeilDefect_MarkerStability_half_bound_iff_covariance_le
import Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_cost_upper
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
private theorem inverse_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (c : ℝ) (hc : 0 < c) :
    operatorInverse (c • A) = c⁻¹ • operatorInverse A := by
  have hunit := (hA.smul hc).isUnit
  have hright : (c • A) * (c⁻¹ • operatorInverse A) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
    exact Ring.mul_inverse_cancel A hA.isUnit
  calc
    operatorInverse (c • A) = operatorInverse (c • A) * 1 := (mul_one _).symm
    _ = operatorInverse (c • A) * ((c • A) * (c⁻¹ • operatorInverse A)) := by rw [hright]
    _ = (operatorInverse (c • A) * (c • A)) * (c⁻¹ • operatorInverse A) := (mul_assoc _ _ _).symm
    _ = c⁻¹ • operatorInverse A := by
      rw [show operatorInverse (c • A) * (c • A) = 1 from Ring.inverse_mul_cancel _ hunit,
        one_mul]

private theorem cost_smul_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_helper A hA c hc]
  ext x
  simp [selectedCost]

private theorem cost_one_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : selectedCost A N ≤ 1 ↔ N ∘L N.adjoint ≤ A := by
  have hh : (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ selectedCost A N ≤ 1 := by
    convert marker_lower_iff_cost_upper A hA N (1 / 2) (by norm_num) using 1 <;> norm_num
  exact hh.symm.trans (half_bound_iff_covariance_le A hA N)
private theorem cost_scaled_helper (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (κ : ℝ) (hκ : 0 < κ) :
    selectedCost A N ≤ κ • (1 : K →L[ℂ] K) ↔ N ∘L N.adjoint ≤ κ • A := by
  rw [← cost_one_helper (κ • A) (hA.smul hκ) N,
    cost_smul_helper A hA N κ hκ]
  constructor
  · intro h
    have hi := smul_le_smul_of_nonneg_left h (inv_pos.mpr hκ).le
    simpa only [smul_smul, inv_mul_cancel₀ hκ.ne', one_smul] using hi
  · intro h
    have hi := smul_le_smul_of_nonneg_left h hκ.le
    simpa only [smul_smul, mul_inv_cancel₀ hκ.ne', one_smul] using hi

end
theorem solution    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : K →L[ℂ] K) ≤ marker A N ↔ N ∘L N.adjoint ≤ (β⁻¹ - 1) • A := by
  have hκ : 0 < β⁻¹ - 1 := by
    have hi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
    linarith
  rw [marker_lower_iff_cost_upper A hA N β hβ,
    cost_scaled_helper A hA N (β⁻¹ - 1) hκ]

