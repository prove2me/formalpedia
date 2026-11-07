-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegralFixInfinity_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:39.412286+00:00
-- url     : https://prove2.me/submissions/391010f9-f27c-4e68-bab4-e2af86fcb6f1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : GL (Fin 2) ℝ)
    (hg : g ∈ (Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range)
    (hc : g 1 0=0) :
    ∃ x : ℝ, g=Matrix.GeneralLinearGroup.upperRightHom x ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom x := by
  rcases hg with ⟨γ,rfl⟩
  have hcZ : γ 1 0=0 := by
    have he : (Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0=(γ 1 0:ℝ) := by
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    rw [he] at hc
    exact_mod_cast hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two,hcZ,mul_zero,sub_zero] at hd
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha,hd⟩|⟨ha,hd⟩
  · refine ⟨(γ 0 1:ℝ),Or.inl ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.GeneralLinearGroup.upperRightHom,
        ha,hd,hcZ]
  · refine ⟨-(γ 0 1:ℝ),Or.inr ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.GeneralLinearGroup.upperRightHom,
        ha,hd,hcZ]
end QEC.Coding.TannerLiftedProduct
