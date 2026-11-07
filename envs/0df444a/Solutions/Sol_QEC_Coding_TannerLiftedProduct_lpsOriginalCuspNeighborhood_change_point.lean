-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_change_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:42.9348+00:00
-- url     : https://prove2.me/submissions/081e1dda-be2e-432c-81f9-a0ae1e07b358

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspChange_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_im
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ')
    (σ : {τ : ℍ // 1<τ.im}) :
    ∃ τ : {τ : ℍ // 1<τ.im}, τ.val.im=σ.val.im ∧
      lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ := by
  obtain ⟨g,hg,x,hx⟩ := lpsOriginalCuspChange_translation N ρ ρ' h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g*e
  have him : 1<(d • σ.val).im := by
    rw [lpsSignedTranslation_im d x hx]
    exact σ.property
  refine ⟨⟨d • σ.val,him⟩,lpsSignedTranslation_im d x hx σ.val,?_⟩
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨g,hg⟩,?_⟩
  change g • (e • σ.val)=r • (d • σ.val)
  simp only [d,mul_smul,smul_inv_smul]
end QEC.Coding.TannerLiftedProduct
