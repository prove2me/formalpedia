-- Prove2me | solution 1 for WeilDefect.MarkerStability.tail_marker_stability
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T05:26:19.91853+00:00
-- url     : https://prove2.me/submissions/71f5f168-43be-4f5e-a884-668c5e73b042

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

theorem cost_mono {A B : H →L[ℂ] H}
    (hAB : A ≤ B) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    selectedCost B N ≤ selectedCost A N := by
  have hi := CStarAlgebra.ringInverse_le_ringInverse hAB hA
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hi)).conj_adjoint N.adjoint
  apply sub_nonneg.mp
  simpa [selectedCost, operatorInverse, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_smul A hA c hc]
  ext x
  simp [selectedCost]

theorem marker_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ marker A N :=
  inverse_nonnegative _ (isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N))

theorem marker_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : marker A N ≤ 1 := by
  have h := CStarAlgebra.ringInverse_le_ringInverse
    (le_add_of_nonneg_right (cost_nonnegative A hA N)) isStrictlyPositive_one
  simpa [marker, operatorInverse] using h

/-- Relative covariance control gives marker control independent of inverse-cost size.
No bound on the selected synthesis or cost is a hypothesis. -/
theorem relative_marker_stability (A B : H →L[ℂ] H) (N : K →L[ℂ] H)
    (hA : IsStrictlyPositive A) (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (hlower : (1 - α) • A ≤ B) (hupper : B ≤ A) :
    IsStrictlyPositive B ∧ 0 ≤ marker A N - marker B N ∧
      ‖marker A N - marker B N‖ ≤ α := by
  have hc : 0 < 1 - α := sub_pos.mpr hα1
  have hB := (hA.smul hc).of_le hlower
  have hSA := cost_nonnegative A hA N
  have hSB := cost_nonnegative B hB N
  have hlo := cost_mono hupper hB N
  have hhi := cost_mono hlower (hA.smul hc) N
  rw [cost_smul A hA N (1 - α) hc] at hhi
  have hΓ : marker B N ≤ marker A N := by
    exact CStarAlgebra.ringInverse_le_ringInverse
      (add_le_add (le_refl 1) hlo) (isStrictlyPositive_one.add_nonneg hSA)
  have hscale : 1 + selectedCost B N ≤ (1 - α)⁻¹ • (1 + selectedCost A N) := by
    rw [smul_add]
    apply add_le_add _ hhi
    have : 1 ≤ (1 - α)⁻¹ := (one_le_inv₀ hc).mpr (by linarith)
    simpa only [one_smul] using
      smul_le_smul_of_nonneg_right this (zero_le_one : (0 : K →L[ℂ] K) ≤ 1)
  have hΓscale : (1 - α) • marker A N ≤ marker B N := by
    have hi := CStarAlgebra.ringInverse_le_ringInverse hscale
      (isStrictlyPositive_one.add_nonneg hSB)
    change operatorInverse ((1 - α)⁻¹ • (1 + selectedCost A N)) ≤ _ at hi
    rw [inverse_smul _ (isStrictlyPositive_one.add_nonneg hSA)
      ((1 - α)⁻¹) (inv_pos.mpr hc), inv_inv] at hi
    exact hi
  have hdiff : 0 ≤ marker A N - marker B N := sub_nonneg.mpr hΓ
  have hbound : marker A N - marker B N ≤ α • (1 : K →L[ℂ] K) := by
    calc
      marker A N - marker B N ≤ marker A N - (1 - α) • marker A N :=
        sub_le_sub_left hΓscale _
      _ = α • marker A N := by rw [sub_smul, one_smul]; abel
      _ ≤ α • (1 : K →L[ℂ] K) :=
        smul_le_smul_of_nonneg_left (marker_le_one A hA N) hα
  refine ⟨hB, hdiff, ?_⟩
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hα hdiff).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using hbound

end WeilDefect.MarkerStability
open WeilDefect.MarkerStability
theorem solution {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (L R : H →L[ℂ] H) (N : K →L[ℂ] H)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (ε α : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α) (hα1 : α < 1) (htail : ‖R‖ ≤ α * ε) :
    IsStrictlyPositive (L + ε • (1 : H →L[ℂ] H) - R) ∧
      0 ≤ marker (L + ε • (1 : H →L[ℂ] H)) N -
        marker (L + ε • (1 : H →L[ℂ] H) - R) N ∧
      ‖marker (L + ε • (1 : H →L[ℂ] H)) N -
        marker (L + ε • (1 : H →L[ℂ] H) - R) N‖ ≤ α := by
  let A := L + ε • (1 : H →L[ℂ] H)
  have hA : IsStrictlyPositive A :=
    IsStrictlyPositive.nonneg_add hL (isStrictlyPositive_one.smul hε)
  have hRbound : R ≤ (α * ε) • (1 : H →L[ℂ] H) := by
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap R (mul_nonneg hα hε.le) hR).mp htail
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  have hεA : ε • (1 : H →L[ℂ] H) ≤ A := le_add_of_nonneg_left hL
  have hRA : R ≤ α • A := by
    calc
      R ≤ (α * ε) • (1 : H →L[ℂ] H) := hRbound
      _ = α • (ε • (1 : H →L[ℂ] H)) := (smul_smul _ _ _).symm
      _ ≤ α • A := smul_le_smul_of_nonneg_left hεA hα
  apply relative_marker_stability A (A - R) N hA α hα hα1
  · calc
      (1 - α) • A = A - α • A := by rw [sub_smul, one_smul]
      _ ≤ A - R := sub_le_sub_left hRA A
  · exact sub_le_self A hR
