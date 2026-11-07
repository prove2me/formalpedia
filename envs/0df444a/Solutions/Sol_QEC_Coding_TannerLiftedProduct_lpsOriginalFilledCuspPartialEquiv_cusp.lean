-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:45.440936+00:00
-- url     : https://prove2.me/submissions/c7e41465-98c3-4e93-bdc5-d7c4e0906fa5

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
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inr (lpsOriginalCuspOrbit N ρ))=0 := rfl
end QEC.Coding.TannerLiftedProduct
