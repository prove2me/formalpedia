-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticPrimeBranch_nome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:43:00.253078+00:00
-- url     : https://prove2.me/submissions/1065e1b3-9e65-4756-a2cd-4dbf474b86ce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranch_finite_point
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranch_infty
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticPrimeBranch p i)=
      lpsOriginalPrimeBranch p i (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ) := by
  cases i with
  | none =>
    rw [lpsOriginalAnalyticPrimeBranch,lpsOriginalAnalyticCuspAffineBranch_nome,
      lpsOriginalPrimeBranch_infty]
    apply congrArg lpsOriginalJInvariant
    apply UpperHalfPlane.ext
    simp only [lpsE2AffineMatrix_action,Nat.cast_mul,Complex.ofReal_zero,add_zero]
    norm_num [mul_assoc]
  | some m =>
    rw [lpsOriginalAnalyticPrimeBranch,lpsOriginalAnalyticCuspAffineBranch_nome]
    apply congrArg lpsOriginalJInvariant
    apply UpperHalfPlane.ext
    rw [lpsE2AffineMatrix_action,lpsOriginalPrimeBranch_finite_point,lpsOriginalJDilated_coe]
    simp only [Nat.cast_one,one_mul]
    push_cast
    have hp : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp [hp]
end QEC.Coding.TannerLiftedProduct
