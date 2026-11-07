-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:27.671243+00:00
-- url     : https://prove2.me/submissions/1bea3c6c-5730-4b87-b09c-8a38816978b0

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
    Continuous (lpsOriginalCuspPunctToFull N ρ) :=
  continuous_subtype_val.subtype_mk _
end QEC.Coding.TannerLiftedProduct
