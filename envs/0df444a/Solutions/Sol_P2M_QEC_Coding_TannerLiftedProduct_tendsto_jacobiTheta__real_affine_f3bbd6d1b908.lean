-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta__real_affine_f3bbd6d1b908
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:15.933365+00:00
-- url     : https://prove2.me/submissions/4c7027b0-aa72-4079-adb8-cac362538b38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta__real_im_infty_452c40a49a1e
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
theorem _root_.solution (a t d : ℝ) (ht : 0<t) :
    Tendsto (fun z : UpperHalfPlane => jacobiTheta₂ (a:ℂ) (((z:ℂ)+(d:ℂ))/(t:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  apply (tendsto_jacobiTheta₂_real_im_infty a).comp
  rw [tendsto_comap_iff]
  have him : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  simpa only [Function.comp_def,Complex.div_ofReal_im,Complex.add_im,Complex.ofReal_im,add_zero,
    UpperHalfPlane.coe_im] using him.atTop_div_const ht
end QEC.Coding.TannerLiftedProduct
