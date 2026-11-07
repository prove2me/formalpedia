-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:03:10.075997+00:00
-- url     : https://prove2.me/submissions/d95fa556-2a40-40d0-825b-bb7f36791c5e

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
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty=(lpsOriginalCuspWidthNat N ρ:ℝ) :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose_spec.2
end QEC.Coding.TannerLiftedProduct
