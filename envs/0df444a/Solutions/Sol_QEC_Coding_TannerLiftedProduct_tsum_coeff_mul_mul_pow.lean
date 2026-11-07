-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_mul_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:24.572625+00:00
-- url     : https://prove2.me/submissions/11875554-f197-4391-89b1-ebe6ac674005

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_mul_mul_pow_eq_antidiagonal_sum

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
    (∑' n : ℕ, ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n) =
      (∑' n : ℕ, ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) *
        (∑' n : ℕ, ((PowerSeries.coeff n T : ℕ) : ℂ) * z ^ n) := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hS hT]
  exact tsum_congr (coeff_mul_mul_pow_eq_antidiagonal_sum S T z)
end QEC.Coding.TannerLiftedProduct
