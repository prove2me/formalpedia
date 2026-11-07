-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:37.812068+00:00
-- url     : https://prove2.me/submissions/b42737c8-bce1-4395-9e61-cd83ea6b7f8d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_integerThetaSeries_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_exp_pi_I_mul_lt_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_integerThetaSeries_eq_jacobiTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_coeff_mul_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_mul_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta τ *
        (jacobiTheta (((2 * r) ^ 2 : ℕ) * τ)) ^ 3 := by
  let z : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let S : PowerSeries ℕ := scaledIntegerThetaSeries (2 * r)
  have hm : 0 < 2 * r := by omega
  have hz : ‖z‖ < 1 := norm_exp_pi_I_mul_lt_one τ hτ
  have hU := summable_norm_coeff_integerThetaSeries_mul_pow z hz
  have hS := summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
    (2 * r) hm z hz
  have hS2 := summable_norm_coeff_mul_mul_pow S S z hS hS
  have hPow : S ^ 3 = (S * S) * S := by ring
  have hS3 : Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n‖) := by
    rw [hPow]
    exact summable_norm_coeff_mul_mul_pow (S * S) S z hS2 hS
  have hEvalS3 :
      (∑' n : ℕ,
        ((PowerSeries.coeff n (S ^ 3) : ℕ) : ℂ) * z ^ n) =
      (∑' n : ℕ,
        ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) ^ 3 := by
    rw [hPow, tsum_coeff_mul_mul_pow (S * S) S z hS2 hS,
      tsum_coeff_mul_mul_pow S S z hS hS]
    ring
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hr]
  change (∑' n : ℕ,
    ((PowerSeries.coeff n (integerThetaSeries * S ^ 3) : ℕ) : ℂ) * z ^ n) = _
  rw [tsum_coeff_mul_mul_pow integerThetaSeries (S ^ 3) z hU hS3,
    hEvalS3]
  rw [show (∑' n : ℕ,
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * z ^ n) =
      jacobiTheta τ by
      simpa [z] using tsum_coeff_integerThetaSeries_eq_jacobiTheta τ hτ]
  rw [show (∑' n : ℕ,
      ((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n) =
      jacobiTheta (((2 * r) ^ 2 : ℕ) * τ) by
      simpa [S, z] using
        tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta (2 * r) hm τ hτ]
end QEC.Coding.TannerLiftedProduct
