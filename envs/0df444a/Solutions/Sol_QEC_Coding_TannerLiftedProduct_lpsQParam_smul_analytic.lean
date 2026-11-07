-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQParam_smul_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:11.327479+00:00
-- url     : https://prove2.me/submissions/557737da-c4dc-433a-b98b-e895bdef3884

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (h : ℝ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ := by
  let f : ℂ → ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have ha : AnalyticAt ℂ (Function.Periodic.qParam h) (f (τ:ℂ)) :=
    (Function.Periodic.contDiff_qParam (h:=h) ω).contDiffAt.analyticAt
  simpa only [Function.comp_def,UpperHalfPlane.ofComplex_apply] using
    ha.comp (f:=f) (UpperHalfPlane.analyticAt_smul hg τ)
end QEC.Coding.TannerLiftedProduct
