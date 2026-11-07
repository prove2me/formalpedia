-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:38:53.03495+00:00
-- url     : https://prove2.me/submissions/f15bf12c-c25c-4e9c-9098-1a091085abf6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_comp_forgetLevel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicPullback_forgetLevel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    lpsOriginalFilledMeromorphicRestrictionSubfield N hN ≤
      lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) := by
  rintro A ⟨F,hF,hA⟩
  refine ⟨F ∘ lpsOriginalFilledForgetLevel N M hNM,
    lpsOriginalFilledChartMeromorphic_comp_forgetLevel N M hNM hN F hF,?_⟩
  rw [lpsOriginalFilledMeromorphicPullback_forgetLevel]
  exact hA
end QEC.Coding.TannerLiftedProduct
