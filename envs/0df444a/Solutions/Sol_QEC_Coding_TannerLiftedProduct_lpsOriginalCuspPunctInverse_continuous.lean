-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:58.255207+00:00
-- url     : https://prove2.me/submissions/ca702c2f-c897-4a13-8e42-e4c7ae52c224

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
    Continuous (lpsOriginalCuspPunctInverse N ρ) :=
  continuous_subtype_val.comp (lpsOriginalCuspNeighborhoodChart N ρ).symm.continuous
end QEC.Coding.TannerLiftedProduct
