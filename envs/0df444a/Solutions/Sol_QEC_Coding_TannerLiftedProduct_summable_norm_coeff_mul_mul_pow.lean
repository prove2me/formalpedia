-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_norm_coeff_mul_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:18.80947+00:00
-- url     : https://prove2.me/submissions/ca311b69-d9f4-43ef-89e8-4d61ea620856

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_mul_mul_pow_eq_antidiagonal_sum
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
    (S T : PowerSeries ℕ) (z : ℂ)
    (hS : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖))
    (hT : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n‖)) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n‖) := by
  have hConv := summable_norm_sum_mul_antidiagonal_of_summable_norm hS hT
  simpa only [← coeff_mul_mul_pow_eq_antidiagonal_sum S T z] using hConv
end QEC.Coding.TannerLiftedProduct
