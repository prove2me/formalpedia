-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.hasSum_lpsStandardTheta_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:50:03.175867+00:00
-- url     : https://prove2.me/submissions/670ca7de-cf7a-400f-93e5-6709e0953472

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_lpsTraceThetaSeries_mul_pow
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
    (r : ℕ) (hr : 0 < r) (z : ℍ) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n)
      (lpsStandardTheta r z) := by
  have hz : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one (by norm_num) z.2
  have hSummable :=
    (summable_norm_coeff_lpsTraceThetaSeries_mul_pow r hr _ hz).of_norm
  have hEq : (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n) =
      lpsStandardTheta r z := by
    simpa [Function.Periodic.qParam] using
      tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta r hr z z.2
  simpa only [hEq] using hSummable.hasSum
end QEC.Coding.TannerLiftedProduct
