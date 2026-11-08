-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cover_cusps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:03:22.223527+00:00
-- url     : https://prove2.me/submissions/abafae6a-8f57-4bb6-b3ed-acb7819c9cff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    ∃ ρ : SL(2,ℤ), Sum.inr c∈(lpsOriginalFilledCuspPartialEquiv N ρ).source := by
  obtain ⟨ρ,rfl⟩ := lpsOriginalCuspOrbit_surjective N c
  exact ⟨ρ,rfl⟩
end QEC.Coding.TannerLiftedProduct
