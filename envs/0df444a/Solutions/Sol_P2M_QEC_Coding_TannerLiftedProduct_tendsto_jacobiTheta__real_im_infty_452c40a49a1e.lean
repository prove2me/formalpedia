-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta__real_im_infty_452c40a49a1e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:16.244457+00:00
-- url     : https://prove2.me/submissions/578e37ea-0cba-464b-a9ea-b14ea1726386

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_isBigO_jacobiTheta__real_sub_one_54a78662520a
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℝ) :
    Tendsto (fun z : ℂ => jacobiTheta₂ (a:ℂ) z) (comap Complex.im atTop) (𝓝 1) := by
  have him : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
  have he : Tendsto (fun z : ℂ => Real.exp (-Real.pi*z.im)) (comap Complex.im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))
  have h := (isBigO_jacobiTheta₂_real_sub_one a).trans_tendsto he
  simpa only [sub_add_cancel,zero_add] using h.add_const 1
end QEC.Coding.TannerLiftedProduct
