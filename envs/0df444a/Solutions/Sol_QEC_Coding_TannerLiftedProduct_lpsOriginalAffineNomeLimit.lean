-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAffineNomeLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:01.47742+00:00
-- url     : https://prove2.me/submissions/6db6926b-cabd-41df-a902-971226b4083e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNome
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1
      ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
  have hq := (UpperHalfPlane.qParam_tendsto_atImInfty
    (by norm_num : (0:ℝ)<1)).pow m
  have h := hq.mul (tendsto_const_nhds (x:=Function.Periodic.qParam 1 (r:ℂ)))
  have hs : Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^m*
      Function.Periodic.qParam 1 (r:ℂ)) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow hm.ne',zero_mul] using h
  exact hs.congr fun τ=>(lpsOriginalAffineNome m hm r τ).symm
end QEC.Coding.TannerLiftedProduct
