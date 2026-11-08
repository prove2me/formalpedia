-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJQuotient_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:46.724125+00:00
-- url     : https://prove2.me/submissions/3a5cf9c1-a15b-41e4-a286-932e629eafce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_nonconstant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    ¬∃ c : ℂ, ∀ x, lpsOriginalJQuotient N x=c := by
  rintro ⟨c,hc⟩
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨c,fun τ => hc ⟦τ⟧⟩
end QEC.Coding.TannerLiftedProduct
