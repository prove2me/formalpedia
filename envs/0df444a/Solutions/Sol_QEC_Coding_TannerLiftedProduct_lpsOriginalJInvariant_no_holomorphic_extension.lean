-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_no_holomorphic_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:48.256092+00:00
-- url     : https://prove2.me/submissions/9a4e0db7-66e7-47c6-baa8-cc4183c2b87e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_nonconstant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_holomorphic_eq_const


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N) :
    ¬∃ f : LPSOriginalFilledCurve N→ℂ,
      (letI := lpsOriginalFilledTopology N;
        letI := lpsOriginalFilledChartedSpace N hN;
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) ∧
      (∀ τ : ℍ, f (Sum.inl ⟦τ⟧)=lpsOriginalJInvariant τ) := by
  rintro ⟨f,hf,hres⟩
  obtain ⟨c,hc⟩ := lpsOriginalFilled_holomorphic_eq_const N hN f hf
  apply lpsOriginalJInvariant_nonconstant
  refine ⟨c,fun τ => ?_⟩
  rw [←hres τ,hc]
  rfl
end QEC.Coding.TannerLiftedProduct
