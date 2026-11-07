-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaCombinationZSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:26:03.847633+00:00
-- url     : https://prove2.me/submissions/c33c905f-3b0f-4092-9db9-b83023b606bf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSigmaCombinationTwelve
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalSigmaCombinationZSeries=
      PowerSeries.C (12:ℚ)⁻¹*
        (PowerSeries.C (5:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3)+
          PowerSeries.C (7:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5)) := by
  ext n
  simp only [PowerSeries.coeff_map,PowerSeries.coeff_C_mul,map_add,
    lpsOriginalSigmaCombinationZSeries,lpsOriginalSigmaZSeries,PowerSeries.coeff_mk]
  norm_cast
  rw [Nat.cast_div (lpsOriginalSigmaCombinationTwelve n) (by norm_num : (12:ℚ)≠0)]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
