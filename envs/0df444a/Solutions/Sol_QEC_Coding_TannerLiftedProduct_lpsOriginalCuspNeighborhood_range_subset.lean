-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:22.942613+00:00
-- url     : https://prove2.me/submissions/81eb8e7b-e89d-4ab1-b206-f18699e68b1b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_change_point

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ')⊆Set.range (lpsOriginalCuspProjection N ρ) := by
  rintro y ⟨σ,rfl⟩
  obtain ⟨τ,ht,he⟩ := lpsOriginalCuspNeighborhood_change_point N ρ ρ' h σ
  exact ⟨τ,he⟩
end QEC.Coding.TannerLiftedProduct
