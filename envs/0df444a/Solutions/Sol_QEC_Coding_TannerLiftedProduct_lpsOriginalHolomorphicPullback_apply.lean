-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicPullback_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:10:48.426204+00:00
-- url     : https://prove2.me/submissions/03284bfd-e416-4c3e-a45c-cf885b538ae3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : 𝒮ℒ)
    (f : LPSOriginalHolomorphicRing) (τ : ℍ) :
    (lpsOriginalHolomorphicPullback g f).val τ=f.val (g.val⁻¹•τ) := rfl
end QEC.Coding.TannerLiftedProduct
