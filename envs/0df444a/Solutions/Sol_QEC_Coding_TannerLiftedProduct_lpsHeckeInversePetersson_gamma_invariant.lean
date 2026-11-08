-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_gamma_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:14.460126+00:00
-- url     : https://prove2.me/submissions/260e3182-b14e-4d3b-ba91-fa1f386e57cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_product_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_conjugate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_mem
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
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (δ • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  obtain ⟨γ,hγ,he⟩ := lpsHeckeConjugateIntersection_conjugate N p δ hδ
  have hδN := (lpsHeckeConjugateIntersection_mem N p δ).mp hδ |>.1
  have hγN := lpsGamma0_product_le N p hγ
  have hi : (lpsHeckeUpperGL ℝ p none)⁻¹*Matrix.SpecialLinearGroup.mapGL ℝ δ =
      Matrix.SpecialLinearGroup.mapGL ℝ γ*(lpsHeckeUpperGL ℝ p none)⁻¹ := by
    have hh := congrArg (fun A : GL (Fin 2) ℝ =>
      (lpsHeckeUpperGL ℝ p none)⁻¹*A*(lpsHeckeUpperGL ℝ p none)⁻¹) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hh.symm
  have hg : (((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) ∣[(2:ℤ)] δ)=
      ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) := by
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) ∣[(2:ℤ)]
      Matrix.SpecialLinearGroup.mapGL ℝ δ)=_
    rw [←SlashAction.slash_mul,hi,SlashAction.slash_mul]
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] γ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N g γ hγN]
  have hp := UpperHalfPlane.petersson_slash_SL 2 (f:ℍ→ℂ)
    ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) δ τ
  simpa only [hg,lpsWeightTwoCusp_slash_gamma0 N f δ hδN] using hp.symm
end QEC.Coding.TannerLiftedProduct
