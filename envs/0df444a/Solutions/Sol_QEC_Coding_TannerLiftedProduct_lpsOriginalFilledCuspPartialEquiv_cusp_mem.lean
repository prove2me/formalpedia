-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:45.502725+00:00
-- url     : https://prove2.me/submissions/3ccdcc8f-af06-4cdc-ba5c-437a807d0152

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Sum.inr (lpsOriginalCuspOrbit N ρ)∈(lpsOriginalFilledCuspPartialEquiv N ρ).source := rfl
end QEC.Coding.TannerLiftedProduct
