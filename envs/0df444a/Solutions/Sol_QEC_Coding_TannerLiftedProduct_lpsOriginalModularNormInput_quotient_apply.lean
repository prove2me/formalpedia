-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_quotient_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:11:11.854518+00:00
-- url     : https://prove2.me/submissions/d8924606-52be-486a-ba1d-d420f120d318

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
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
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (c : ℂ)
    (q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    (τ : ℍ) :
    SlashInvariantForm.quotientFunc (lpsOriginalModularNormInput N hN c) q τ=
      SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ-
        c*SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hd : (g.val⁻¹).det=1 := Subgroup.HasDetOne.det_eq (inv_mem g.property)
    have hp : 0<(g.val⁻¹).det.val := by rw [hd]; norm_num
    simp only [SlashInvariantForm.quotientFunc_mk,lpsOriginalModularNormInput,
      FunLike.coe_sub,FunLike.coe_smul,ModularForm.slash_apply,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,UpperHalfPlane.σ,if_pos hp,
      ContinuousAlgEquiv.refl_apply]
    ring
end QEC.Coding.TannerLiftedProduct
