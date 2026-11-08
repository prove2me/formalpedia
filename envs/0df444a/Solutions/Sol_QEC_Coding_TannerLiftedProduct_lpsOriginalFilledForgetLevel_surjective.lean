-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:21.961648+00:00
-- url     : https://prove2.me/submissions/3480443a-4500-4af1-ace6-12e0de929526

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_surjective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalFilledForgetLevel N M hNM) := by
  intro y
  cases y with
  | inl y =>
    obtain ⟨x, hx⟩ := lpsOriginalInteriorForgetLevel_surjective N M hNM y
    exact ⟨Sum.inl x, congrArg Sum.inl hx⟩
  | inr c =>
    obtain ⟨x, hx⟩ := lpsOriginalCuspForgetLevel_surjective N M hNM c
    exact ⟨Sum.inr x, congrArg Sum.inr hx⟩
end QEC.Coding.TannerLiftedProduct
