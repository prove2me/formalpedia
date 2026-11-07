-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_qParam_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:04:13.163029+00:00
-- url     : https://prove2.me/submissions/a8fb6efa-a55b-4fc1-a858-a1338c3eaadd

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
theorem _root_.solution (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)*lpsOriginalJInvariant τ=
      lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ:ℂ)) := by
  have hq := Function.Periodic.qParam_ne_zero (h:=1) (τ:ℂ)
  have hD0 := CuspFormClass.cuspFunction_apply_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  have hE : UpperHalfPlane.cuspFunction 1 ModularForm.E₄
      (Function.Periodic.qParam 1 (τ:ℂ))=ModularForm.E₄ τ :=
    (UpperHalfPlane.eq_cuspFunction τ one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
        one_mem_strictPeriods_SL))
  have hD : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant
      (Function.Periodic.qParam 1 (τ:ℂ))=ModularForm.discriminant τ :=
    (UpperHalfPlane.eq_cuspFunction τ one_ne_zero
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL))
  change UpperHalfPlane.cuspFunction 1 ModularForm.discriminant 0=0 at hD0
  rw [lpsOriginalJInvariant,lpsOriginalJQCoefficient,dslope_of_ne _ hq,
    slope,hD0,hE,hD]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  field_simp [hq,ModularForm.discriminant_ne_zero τ]
end QEC.Coding.TannerLiftedProduct
