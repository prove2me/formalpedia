-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_norm_theta_coeff_mul_pow_of_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:35.05263+00:00
-- url     : https://prove2.me/submissions/51a69ae7-2dad-4637-b303-60150454bc93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (S : PowerSeries ℕ)
    (hCoeff : ∀ n : ℕ, PowerSeries.coeff n S ≤ 2)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖) := by
  have hGeom : Summable (fun n : ℕ => (‖z‖ : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa using hz)
  apply (hGeom.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  simpa only [norm_mul, norm_pow, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_right
      (show ((PowerSeries.coeff n S : ℕ) : ℝ) ≤ 2 by exact_mod_cast hCoeff n)
      (pow_nonneg (norm_nonneg z) _)
end QEC.Coding.TannerLiftedProduct
