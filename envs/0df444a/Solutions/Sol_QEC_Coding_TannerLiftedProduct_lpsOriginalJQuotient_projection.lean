-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJQuotient_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:40.543854+00:00
-- url     : https://prove2.me/submissions/ab06f02c-16d2-436b-af90-0a64d04ac671

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
theorem _root_.solution (N : ℕ) (τ : ℍ) :
    lpsOriginalJQuotient N ⟦τ⟧=lpsOriginalJInvariant τ := rfl
end QEC.Coding.TannerLiftedProduct
