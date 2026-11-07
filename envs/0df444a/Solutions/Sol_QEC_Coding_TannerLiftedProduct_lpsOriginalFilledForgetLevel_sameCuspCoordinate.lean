-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_sameCuspCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:28.610613+00:00
-- url     : https://prove2.me/submissions/a2ea52c0-a293-448d-af1e-002481dc7a92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cusp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (x : LPSOriginalFilledCurve M)
    (hx : x ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source) :
    lpsOriginalFilledCuspPartialEquiv N ρ (lpsOriginalFilledForgetLevel N M hNM x) =
      (lpsOriginalFilledCuspPartialEquiv M ρ x) ^ lpsOriginalCuspLevelDegree N M ρ := by
  cases x with
  | inl y =>
    change y ∈ Set.range (lpsOriginalCuspProjection M ρ) at hx
    obtain ⟨σ, rfl⟩ := hx
    change lpsOriginalFilledCuspPartialEquiv N ρ
      (Sum.inl (lpsOriginalCuspProjection N ρ σ)) = _
    rw [lpsOriginalFilledCuspPartialEquiv_projection,
      lpsOriginalFilledCuspPartialEquiv_projection]
    exact (lpsOriginalCuspLevelDegree_qParam N M hNM ρ σ.val).symm
  | inr c =>
    change c = lpsOriginalCuspOrbit M ρ at hx
    subst c
    rw [lpsOriginalFilledForgetLevel_cusp, lpsOriginalFilledCuspPartialEquiv_cusp,
      lpsOriginalFilledCuspPartialEquiv_cusp]
    exact (zero_pow (Nat.ne_of_gt (lpsOriginalCuspLevelDegree_positive N M hNM ρ))).symm
end QEC.Coding.TannerLiftedProduct
