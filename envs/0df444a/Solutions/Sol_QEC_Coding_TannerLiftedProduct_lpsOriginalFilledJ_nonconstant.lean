-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:58.631208+00:00
-- url     : https://prove2.me/submissions/c1aabcac-cfbe-401f-89a4-ebd8bd415e4b

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
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJ N x=c := by
  rintro ⟨c,hc⟩
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨c,fun τ => hc (Sum.inl ⟦τ⟧)⟩
end QEC.Coding.TannerLiftedProduct
