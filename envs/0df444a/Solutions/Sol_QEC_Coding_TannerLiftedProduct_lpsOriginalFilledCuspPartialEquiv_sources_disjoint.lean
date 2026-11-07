-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_sources_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:07.785777+00:00
-- url     : https://prove2.me/submissions/bf2c8716-f15c-4df1-8d58-329b0671f837

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhood_disjoint


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (lpsOriginalFilledCuspPartialEquiv N ρ).source
      (lpsOriginalFilledCuspPartialEquiv N ρ').source := by
  apply Set.disjoint_left.mpr
  intro x hρ hρ'
  cases x with
  | inl y =>
    exact Set.disjoint_left.mp (lpsOriginalCuspNeighborhood_disjoint N ρ ρ' h) hρ hρ'
  | inr c =>
    exact h (hρ.symm.trans hρ')
end QEC.Coding.TannerLiftedProduct
