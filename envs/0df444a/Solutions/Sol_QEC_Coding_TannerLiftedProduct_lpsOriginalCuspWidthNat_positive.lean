-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:02:58.652539+00:00
-- url     : https://prove2.me/submissions/9af50261-a688-42c1-9820-365d3aa7ff4a

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
    0<lpsOriginalCuspWidthNat N ρ :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose_spec.1
end QEC.Coding.TannerLiftedProduct
