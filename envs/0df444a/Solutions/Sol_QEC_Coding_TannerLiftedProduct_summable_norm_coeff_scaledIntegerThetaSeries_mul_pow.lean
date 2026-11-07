-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_norm_coeff_scaledIntegerThetaSeries_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:45.15923+00:00
-- url     : https://prove2.me/submissions/514b7081-2e43-483a-991c-d5bb3f6ef77b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_theta_coeff_mul_pow_of_le_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_integerSquareRoots
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaledIntegerSquareRoots_eq_empty_of_not_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaledIntegerSquareRoots_eq_of_dvd
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) * z ^ n‖) := by
  apply summable_norm_theta_coeff_mul_pow_of_le_two (scaledIntegerThetaSeries m) _ z hz
  intro n
  rw [coeff_scaledIntegerThetaSeries]
  by_cases hdiv : m ^ 2 ∣ n
  · rw [scaledIntegerSquareRoots_eq_of_dvd hm hdiv, card_integerSquareRoots]
    split_ifs <;> omega
  · rw [scaledIntegerSquareRoots_eq_empty_of_not_dvd hm hdiv]
    simp
end QEC.Coding.TannerLiftedProduct
