-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:04:00.585518+00:00
-- url     : https://prove2.me/submissions/822a164d-02b6-4d8e-9634-3daac1dae730

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) lpsOriginalJInvariant := by
  exact ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (ModularFormClass.holo CuspForm.discriminant) ModularForm.discriminant_ne_zero
end QEC.Coding.TannerLiftedProduct
