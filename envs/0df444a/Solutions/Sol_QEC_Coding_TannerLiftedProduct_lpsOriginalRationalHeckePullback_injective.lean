-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:12:08.721439+00:00
-- url     : https://prove2.me/submissions/02963e64-e2ca-401a-8921-9eeebb863747

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    Function.Injective (lpsOriginalRationalHeckePullback N p hN hp h4N) :=
  (lpsOriginalRationalHeckePullback N p hN hp h4N).injective
end QEC.Coding.TannerLiftedProduct
