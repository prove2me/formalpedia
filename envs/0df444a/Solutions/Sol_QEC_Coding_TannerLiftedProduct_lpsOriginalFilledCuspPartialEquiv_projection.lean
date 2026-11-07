-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:41:18.326205+00:00
-- url     : https://prove2.me/submissions/7dbf2974-c7e9-48cc-8d21-09aa15c6ec83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhoodChart_projection


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inl (lpsOriginalCuspProjection N ρ τ))=
      Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ.val := by
  have h : lpsOriginalCuspProjection N ρ τ∈Set.range (lpsOriginalCuspProjection N ρ) :=
    ⟨τ,rfl⟩
  change lpsOriginalFilledCuspToFun N ρ (Sum.inl (lpsOriginalCuspProjection N ρ τ))=_
  rw [lpsOriginalFilledCuspToFun,dif_pos h]
  exact congrArg Subtype.val (lpsOriginalCuspNeighborhoodChart_projection N ρ τ)
end QEC.Coding.TannerLiftedProduct
