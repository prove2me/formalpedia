-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_slash_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:09.084204+00:00
-- url     : https://prove2.me/submissions/3eff519b-5e70-4ac9-b2a1-22e2e6602cfe

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : GL (Fin 2) ℝ)
    (hM : 0<M.det.val) (τ : ℍ) :
    (M.det.val:ℂ)^2 * ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] M) τ^3 /
      ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] M) τ = lpsOriginalJInvariant (M•τ) := by
  have hd : (M.det.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hM.ne'
  simp only [ModularForm.slash_apply,UpperHalfPlane.σ,hM,if_pos,abs_of_pos hM,
    Int.reduceSub,Int.reduceNeg,zpow_neg,zpow_ofNat,lpsOriginalJInvariant,
    ContinuousAlgEquiv.refl_apply]
  change (M.det.val:ℂ)^2 * (ModularForm.E₄ (M•τ) * (M.det.val:ℂ)^3 *
    ((UpperHalfPlane.denom M τ)^4)⁻¹)^3 /
    (ModularForm.discriminant (M•τ)*(M.det.val:ℂ)^11*((UpperHalfPlane.denom M τ)^12)⁻¹)=_
  field_simp [hd,UpperHalfPlane.denom_ne_zero M τ,ModularForm.discriminant_ne_zero (M•τ)]
end QEC.Coding.TannerLiftedProduct
