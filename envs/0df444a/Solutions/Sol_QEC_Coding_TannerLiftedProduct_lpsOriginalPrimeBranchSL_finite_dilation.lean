-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:44:35.141384+00:00
-- url     : https://prove2.me/submissions/e382999d-2e98-4363-a69d-ed9fad3b0ccf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_finite_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_coe
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
    (m : Fin p) (τ : ℍ) :
    lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 •
      (lpsOriginalPrimeBranchSL p (some m) • τ)=
      ModularGroup.S • (lpsHeckeUpperGL ℝ p (some m) • τ) := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe,lpsOriginalPrimeBranchSL_finite_coe,
    UpperHalfPlane.modular_S_smul]
  change (p:ℂ)*(-1/((τ:ℂ)+(m.val:ℂ)))=
    (-((lpsHeckeUpperGL ℝ p (some m) • τ : ℍ) : ℂ))⁻¹
  rw [lpsHeckeUpperGL_finite_action]
  rw [inv_neg,inv_div]
  simp only [div_eq_mul_inv]
  ring
end QEC.Coding.TannerLiftedProduct
