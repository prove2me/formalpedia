-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDeltaPowerAtLevel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:21.297436+00:00
-- url     : https://prove2.me/submissions/9e825862-db8f-4cc1-aaa1-e58fc25f917a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N k : ℕ) (τ : ℍ) :
    lpsOriginalMeromorphicDeltaPowerAtLevel N k τ = ModularForm.discriminant τ ^ k := by
  change ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k) τ = _
  rw [ModularForm.coe_pow]
  rfl
end QEC.Coding.TannerLiftedProduct
