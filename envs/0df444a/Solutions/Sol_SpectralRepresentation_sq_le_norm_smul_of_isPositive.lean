-- Prove2me | solution 1 for SpectralRepresentation.sq_le_norm_smul_of_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:40.096801+00:00
-- url     : https://prove2.me/submissions/884e5d29-874e-4360-a00e-16adc9bf5933

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
namespace SpectralRepresentation
theorem _root_.solution {A : H →L[ℂ] H} (hA : A.IsPositive) :
    A ^ 2 ≤ (‖A‖ : ℝ) • A := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have h0A : (0 : H →L[ℂ] H) ≤ A := by
    rw [ContinuousLinearMap.le_def, sub_zero]; exact hA
  rw [← sub_nonneg]
  have key : (‖A‖ : ℝ) • A - A ^ 2 = cfc (fun t : ℝ => ‖A‖ * t - t ^ 2) A := by
    rw [cfc_sub _ _ A, cfc_const_mul .., cfc_pow_id .., cfc_id' ..]
  rw [key]
  apply cfc_nonneg
  intro t ht
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg h0A ht
  have htle : t ≤ ‖A‖ := by
    have := spectrum.norm_le_norm_of_mem ht
    rwa [Real.norm_eq_abs, abs_of_nonneg ht0] at this
  nlinarith [ht0, htle]
end SpectralRepresentation
