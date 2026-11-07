-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_norm_coeff_integerThetaSeries_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:30.746287+00:00
-- url     : https://prove2.me/submissions/23b6f2ce-45d6-486e-a269-b7c8ea1050eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_theta_coeff_mul_pow_of_le_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_eq_ite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * z ^ n‖) := by
  apply summable_norm_theta_coeff_mul_pow_of_le_two integerThetaSeries _ z hz
  intro n
  rw [coeff_integerThetaSeries_eq_ite]
  split_ifs <;> omega
end QEC.Coding.TannerLiftedProduct
