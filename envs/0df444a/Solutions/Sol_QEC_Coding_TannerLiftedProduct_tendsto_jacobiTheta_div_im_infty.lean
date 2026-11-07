-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_jacobiTheta_div_im_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:33.129073+00:00
-- url     : https://prove2.me/submissions/7ea6bb9d-0753-4a46-80b6-58f083fdef6d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta_im_infty
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
    Tendsto (fun z : UpperHalfPlane => jacobiTheta ((z:ℂ)/(c:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  apply tendsto_jacobiTheta_im_infty.comp
  rw [tendsto_comap_iff]
  have him : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  simpa only [Function.comp_def,Complex.div_ofReal_im,UpperHalfPlane.coe_im] using
    him.atTop_div_const hc
end QEC.Coding.TannerLiftedProduct
