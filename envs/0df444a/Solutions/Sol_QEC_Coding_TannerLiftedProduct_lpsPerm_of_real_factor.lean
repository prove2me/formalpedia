-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPerm_of_real_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:49.626739+00:00
-- url     : https://prove2.me/submissions/8ed29e9b-1ae0-4a47-9edf-bf94c0b73f5f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGLPermSL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (A : GL (Fin 2) ℝ) (γ δ : SL(2,ℤ))
    (he : A*Matrix.SpecialLinearGroup.mapGL ℝ γ=
      Matrix.SpecialLinearGroup.mapGL ℝ δ*A) :
    (MulAut.conj (MulAction.toPerm A : Equiv.Perm ℍ))
      (MulAction.toPerm γ : Equiv.Perm ℍ)=(MulAction.toPerm δ : Equiv.Perm ℍ) := by
  have h' : A*Matrix.SpecialLinearGroup.mapGL ℝ γ*A⁻¹=Matrix.SpecialLinearGroup.mapGL ℝ δ := by
    rw [he,mul_assoc,mul_inv_cancel,mul_one]
  have hp := congrArg (MulAction.toPermHom (GL (Fin 2) ℝ) ℍ) h'
  simp only [map_mul,map_inv] at hp
  change (MulAction.toPerm A : Equiv.Perm ℍ) *
    (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ γ) : Equiv.Perm ℍ) *
      (MulAction.toPerm A : Equiv.Perm ℍ)⁻¹ =
        (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ δ) : Equiv.Perm ℍ) at hp
  simpa only [MulAut.conj_apply,lpsGLPermSL] using hp
end QEC.Coding.TannerLiftedProduct
