-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:59.936257+00:00
-- url     : https://prove2.me/submissions/cc2341b9-ad18-433d-a9ec-5d095a75a02a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspProjection_openRange


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctInverse N ρ) :=
  (lpsOriginalCuspProjection_openRange N ρ).isOpenMap_subtype_val.comp
    (lpsOriginalCuspNeighborhoodChart N ρ).symm.isOpenMap
end QEC.Coding.TannerLiftedProduct
