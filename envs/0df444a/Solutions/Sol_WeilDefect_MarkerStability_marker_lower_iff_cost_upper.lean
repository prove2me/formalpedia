-- Prove2me | solution 1 for WeilDefect.MarkerStability.marker_lower_iff_cost_upper
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T15:38:24.318552+00:00
-- url     : https://prove2.me/submissions/23e0ed5b-4b51-4cf1-8198-923f13828fa9

import Definitions.Def_WeilMarker_regularized_cost
set_option autoImplicit false
open scoped InnerProduct ComplexOrder
open ContinuousLinearMap
noncomputable section
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem inverse_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ operatorInverse A := by
  rw [operatorInverse, Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)

theorem inverse_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
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

theorem cost_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ selectedCost A N := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (inverse_nonnegative A hA)).conj_adjoint N.adjoint
  simpa [selectedCost] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_le_of_marker_lower (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (β : ℝ) (hβ : 0 < β)
    (hb : β • (1 : K →L[ℂ] K) ≤ marker A N) :
    selectedCost A N ≤ (β⁻¹ - 1) • 1 := by
  have hs := isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N)
  have hi := CStarAlgebra.ringInverse_le_ringInverse hb (isStrictlyPositive_one.smul hβ)
  change operatorInverse (marker A N) ≤ operatorInverse (β • 1) at hi
  rw [show operatorInverse (marker A N) = 1 + selectedCost A N from Ring.inverse_inverse hs.isUnit,
    inverse_smul _ isStrictlyPositive_one β hβ] at hi
  simp only [operatorInverse, Ring.inverse_one] at hi
  rw [sub_smul, one_smul]
  exact (le_sub_iff_add_le).mpr (by simpa only [add_comm] using hi)


end WeilDefect.MarkerStability
open WeilDefect.MarkerStability
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem solution (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (β : ℝ) (hβ : 0 < β) :
    β • (1 : K →L[ℂ] K) ≤ marker A N ↔
      selectedCost A N ≤ (β⁻¹ - 1) • (1 : K →L[ℂ] K) := by
  constructor
  · exact cost_le_of_marker_lower A hA N β hβ
  · intro h
    have hs := isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N)
    have hb : 1 + selectedCost A N ≤ β⁻¹ • (1 : K →L[ℂ] K) := by
      rw [sub_smul, one_smul] at h
      simpa only [add_comm] using le_sub_iff_add_le.mp h
    have hi := CStarAlgebra.ringInverse_le_ringInverse hb hs
    change WeilDefect.WDT13.operatorInverse (β⁻¹ • (1 : K →L[ℂ] K)) ≤ marker A N at hi
    rw [inverse_smul _ isStrictlyPositive_one β⁻¹ (inv_pos.mpr hβ)] at hi
    simpa [WeilDefect.WDT13.operatorInverse] using hi

