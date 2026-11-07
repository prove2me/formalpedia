-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspSource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:24.093846+00:00
-- url     : https://prove2.me/submissions/e8519441-9934-4d17-9d3a-c00a216f3b64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_projection


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledForgetLevel N M hNM x ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source := by
  cases x with
  | inl y =>
    change y ∈ Set.range (lpsOriginalCuspProjection M ρ) at hx
    obtain ⟨σ, rfl⟩ := hx
    exact ⟨σ, rfl⟩
  | inr c =>
    change c = lpsOriginalCuspOrbit M ρ at hx
    subst c
    change lpsOriginalCuspForgetLevel N M hNM (lpsOriginalCuspOrbit M ρ) =
      lpsOriginalCuspOrbit N ρ
    exact lpsOriginalCuspForgetLevel_projection N M hNM ρ
end QEC.Coding.TannerLiftedProduct
