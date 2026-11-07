-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:06.469995+00:00
-- url     : https://prove2.me/submissions/a7bf4af3-4b28-4217-b6c5-6ae80c701e38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_range_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ)=Set.range (lpsOriginalCuspProjection N ρ') :=
  Set.Subset.antisymm (lpsOriginalCuspNeighborhood_range_subset N ρ' ρ h.symm)
    (lpsOriginalCuspNeighborhood_range_subset N ρ ρ' h)
end QEC.Coding.TannerLiftedProduct
