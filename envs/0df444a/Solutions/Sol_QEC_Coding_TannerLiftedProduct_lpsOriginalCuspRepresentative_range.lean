-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:33.652217+00:00
-- url     : https://prove2.me/submissions/be8d649e-5235-4b60-9977-fd5bea6b0194

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_range_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set.range (lpsOriginalCuspProjection N
      (lpsOriginalCuspRepresentative N (lpsOriginalCuspOrbit N ρ)))=
        Set.range (lpsOriginalCuspProjection N ρ) :=
  lpsOriginalCuspNeighborhood_range_eq N _ ρ (lpsOriginalCuspRepresentative_orbit N _)
end QEC.Coding.TannerLiftedProduct
