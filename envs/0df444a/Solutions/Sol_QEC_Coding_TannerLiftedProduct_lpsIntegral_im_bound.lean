-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegral_im_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:38.076242+00:00
-- url     : https://prove2.me/submissions/250af8d0-8e46-4251-95ad-d1d963117da9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralFixInfinity_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_im
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
theorem _root_.solution (g : GL (Fin 2) ℝ)
    (hg : g∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range) (τ : ℍ) :
    (g • τ).im≤ max τ.im (1/τ.im) := by
  by_cases hc : g 1 0=0
  · obtain ⟨x,hx⟩ := lpsIntegralFixInfinity_translation g hg hc
    rw [lpsSignedTranslation_im g x hx]
    exact le_max_left _ _
  · rcases hg with ⟨γ,rfl⟩
    have he : (Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0=(γ 1 0:ℝ) := by
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have hcZ : γ 1 0≠0 := by
      intro hz
      apply hc
      rw [he,hz];simp
    have hZ : (1:ℤ)≤(γ 1 0)^2 := by
      have hp := sq_pos_of_ne_zero hcZ
      omega
    have hR : (1:ℝ)≤((Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0)^2 := by
      rw [he]
      exact_mod_cast hZ
    have hd := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
    have hi := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
    simp only [Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,abs_one,one_mul] at hi
    rw [hi]
    have hb : τ.im^2≤Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg τ.im)]
    calc
      _≤τ.im/τ.im^2 := div_le_div_of_nonneg_left τ.im_pos.le (sq_pos_of_pos τ.im_pos) hb
      _=1/τ.im := by field_simp
      _≤ max τ.im (1/τ.im) := le_max_right _ _
end QEC.Coding.TannerLiftedProduct
