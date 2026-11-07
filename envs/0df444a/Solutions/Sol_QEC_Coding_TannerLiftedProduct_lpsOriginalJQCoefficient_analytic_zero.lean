-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJQCoefficient_analytic_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:03:40.267791+00:00
-- url     : https://prove2.me/submissions/041473c6-ebb9-42af-8d4c-fbd985ca8534

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    AnalyticAt ℂ lpsOriginalJQCoefficient 0 := by
  have hE := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
    one_pos one_mem_strictPeriods_SL
  have hD := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  obtain ⟨P,hP⟩ := hD
  have hd : AnalyticAt ℂ (dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  have hv : dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 0=1 := by
    simpa [dslope_same,UpperHalfPlane.qExpansion_coeff,iteratedDeriv_one] using
      ModularForm.discriminant_qExpansion_coeff_one
  exact (hE.pow 3).div hd (by rw [hv];norm_num)
end QEC.Coding.TannerLiftedProduct
