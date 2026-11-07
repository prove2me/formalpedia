-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_norm_coeff_lpsTraceThetaSeries_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:38.918195+00:00
-- url     : https://prove2.me/submissions/6e94a676-7474-4d8a-957f-d4150a53c209

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_integerThetaSeries_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_mul_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) * z ^ n‖) := by
  let S : PowerSeries ℕ := scaledIntegerThetaSeries (2 * r)
  have hm : 0 < 2 * r := by omega
  have hU := summable_norm_coeff_integerThetaSeries_mul_pow z hz
  have hS := summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (2 * r) hm z hz
  have hS2 := summable_norm_coeff_mul_mul_pow S S z hS hS
  have hPow : S ^ 3 = (S * S) * S := by ring
  have hS3 : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n‖) := by
    rw [hPow]
    exact summable_norm_coeff_mul_mul_pow (S * S) S z hS2 hS
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hr]
  change Summable (fun n : ℕ =>
    ‖((PowerSeries.coeff n (integerThetaSeries * S ^ 3) : ℕ) : ℂ) * z ^ n‖)
  exact summable_norm_coeff_mul_mul_pow integerThetaSeries (S ^ 3) z hU hS3
end QEC.Coding.TannerLiftedProduct
