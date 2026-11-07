-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:09.66431+00:00
-- url     : https://prove2.me/submissions/1595fadc-e2a8-449b-9d26-d247eea8d033

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_overlap_cuspOrbit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (Set.range (lpsOriginalCuspProjection N ρ))
      (Set.range (lpsOriginalCuspProjection N ρ')) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨τ,rfl⟩ ⟨σ,he⟩
  exact h (lpsOriginalCuspNeighborhood_overlap_cuspOrbit N ρ ρ' τ σ he.symm)
end QEC.Coding.TannerLiftedProduct
