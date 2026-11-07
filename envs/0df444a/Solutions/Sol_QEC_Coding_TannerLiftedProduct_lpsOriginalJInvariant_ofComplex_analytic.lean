-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_ofComplex_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:35.246171+00:00
-- url     : https://prove2.me/submissions/5de2ff94-d5b7-4b93-8598-c3bf12bb5505

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (τ : ℍ) :
    AnalyticAt ℂ (lpsOriginalJInvariant∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ (lpsOriginalJInvariant∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (lpsOriginalJInvariant_holomorphic ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)
end QEC.Coding.TannerLiftedProduct
