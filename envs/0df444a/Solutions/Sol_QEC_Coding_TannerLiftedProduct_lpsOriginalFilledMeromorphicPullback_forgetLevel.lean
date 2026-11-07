-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_forgetLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:08:57.007407+00:00
-- url     : https://prove2.me/submissions/2e1b444a-0f1d-46cb-87b9-e0c769cf9acd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) (hNM : N ∣ M) (F : LPSOriginalFilledCurve N → ℂ) :
    lpsOriginalFilledMeromorphicPullback M
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) =
      lpsOriginalFilledMeromorphicPullback N F := by
  funext z
  rfl
end QEC.Coding.TannerLiftedProduct
