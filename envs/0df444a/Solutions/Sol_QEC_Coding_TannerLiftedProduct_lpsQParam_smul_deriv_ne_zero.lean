-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQParam_smul_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:19.351474+00:00
-- url     : https://prove2.me/submissions/4fc45e92-f182-4f3e-a904-6b38c769e201

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_deriv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (h : ℝ) (hh : h≠0) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ≠0 := by
  let f : ℂ → ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have hf := UpperHalfPlane.hasStrictDerivAt_smul hg τ |>.hasDerivAt
  have hq := (Function.Periodic.differentiable_qParam (h:=h)).differentiableAt (x:=f τ)
  change deriv (Function.Periodic.qParam h ∘ f) (τ:ℂ)≠0
  rw [deriv_comp (τ:ℂ) hq hf.differentiableAt,lpsQParam_deriv]
  apply mul_ne_zero
  · exact mul_ne_zero
      (div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hh))
      (Function.Periodic.qParam_ne_zero (f τ))
  · exact UpperHalfPlane.deriv_smul_ne_zero hg τ
end QEC.Coding.TannerLiftedProduct
