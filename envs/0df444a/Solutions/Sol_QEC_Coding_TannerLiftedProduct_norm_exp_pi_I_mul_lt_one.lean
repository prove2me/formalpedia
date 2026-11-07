-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.norm_exp_pi_I_mul_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:40.017212+00:00
-- url     : https://prove2.me/submissions/4d69e8d6-7793-4b6b-b0d3-7dddcf17405d

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
theorem _root_.solution (τ : ℂ) (hτ : 0 < τ.im) :
    ‖Complex.exp (Real.pi * Complex.I * τ)‖ < 1 := by
  rw [Complex.norm_exp]
  have hRe : (Real.pi * Complex.I * τ).re = -Real.pi * τ.im := by
    simp [Complex.mul_re]
  rw [hRe]
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos
    (neg_lt_zero.mpr Real.pi_pos) hτ)
end QEC.Coding.TannerLiftedProduct
