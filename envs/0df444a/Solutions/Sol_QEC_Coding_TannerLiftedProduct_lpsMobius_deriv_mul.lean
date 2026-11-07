-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsMobius_deriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:59.339275+00:00
-- url     : https://prove2.me/submissions/b7afec14-c227-4f61-9bd9-9e517578fab2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r g : GL (Fin 2) ℝ)
    (hr : 0<r.val.det) (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => ((r*g) • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ=
      deriv (fun z : ℂ => (r • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) (g • τ : ℍ) *
      deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ := by
  let a : ℂ→ℂ := fun z => (r • UpperHalfPlane.ofComplex z : ℍ)
  let b : ℂ→ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have he : (fun z : ℂ => ((r*g) • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ)=a∘b := by
    funext z
    simp only [a,b,Function.comp_def,UpperHalfPlane.ofComplex_apply,mul_smul]
  rw [he]
  have ha : DifferentiableAt ℂ a (b (τ:ℂ)) := by
    simpa only [b,UpperHalfPlane.ofComplex_apply] using
      (UpperHalfPlane.hasStrictDerivAt_smul hr (g • τ)).hasDerivAt.differentiableAt
  have hb : DifferentiableAt ℂ b (τ:ℂ) :=
    (UpperHalfPlane.hasStrictDerivAt_smul hg τ).hasDerivAt.differentiableAt
  simpa only [a,b,UpperHalfPlane.ofComplex_apply] using deriv_comp (τ:ℂ) ha hb
end QEC.Coding.TannerLiftedProduct
