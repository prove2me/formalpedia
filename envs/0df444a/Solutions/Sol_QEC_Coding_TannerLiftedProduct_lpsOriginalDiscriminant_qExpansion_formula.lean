-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDiscriminant_qExpansion_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:47:27.076214+00:00
-- url     : https://prove2.me/submissions/091288cd-9c8f-495d-b336-ae1c9bc6ea0b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubeSubE6SquareForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubeSubE6SquareForm_qExpansion
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
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    qExpansion 1 ModularForm.discriminant=(1728:ℂ)⁻¹ •
      ((qExpansion 1 ModularForm.E₄)^3-(qExpansion 1 ModularForm.E₆)^2) := by
  have he : (ModularForm.discriminant : ℍ→ℂ)=
      ((1728:ℂ)⁻¹ • lpsOriginalE4CubeSubE6SquareForm : ModularForm 𝒮ℒ 12) := by
    funext τ
    simp only [smul_apply,lpsOriginalE4CubeSubE6SquareForm_apply]
    simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [he,FunLike.coe_smul,ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    lpsOriginalE4CubeSubE6SquareForm_qExpansion]
end QEC.Coding.TannerLiftedProduct
