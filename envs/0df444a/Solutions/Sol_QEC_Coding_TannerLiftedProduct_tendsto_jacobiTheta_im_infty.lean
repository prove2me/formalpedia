-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_jacobiTheta_im_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:36.401542+00:00
-- url     : https://prove2.me/submissions/f25c35c8-5c99-4bb9-a464-9c965048f244

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
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
theorem _root_.solution :
    Tendsto jacobiTheta (comap Complex.im atTop) (𝓝 1) := by
  have him : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
  have hexp : Tendsto (fun z : ℂ => Real.exp (-Real.pi * z.im))
      (comap Complex.im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))
  have h := isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto hexp
  simpa only [sub_add_cancel,zero_add] using h.add_const 1
end QEC.Coding.TannerLiftedProduct
