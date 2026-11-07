-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_jacobiTheta_mul_im_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:22.490396+00:00
-- url     : https://prove2.me/submissions/bea2ebc5-36fe-4f8e-aa59-e81b2b799ec5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta_div_im_infty
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (c : ℝ) (hc : 0 < c) :
    Tendsto (fun z : UpperHalfPlane => jacobiTheta ((c:ℂ)*(z:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := tendsto_jacobiTheta_div_im_infty (1/c) (by positivity)
  simpa only [one_div,Complex.ofReal_inv,div_eq_mul_inv,inv_inv,mul_one,mul_comm] using h
end QEC.Coding.TannerLiftedProduct
