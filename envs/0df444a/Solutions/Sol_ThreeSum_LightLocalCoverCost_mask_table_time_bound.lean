-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.mask_table_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:57.872193+00:00
-- url     : https://prove2.me/submissions/49caa928-b6a4-4d93-830c-9d8566989ffc

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightWeightGather_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverCost
theorem _root_.solution (L n : ℕ) :
    LightMaskBitTable.time L n ≤ 400*(n+1)*(L+1)^2 := by
  have hm := Nat.mul_le_mul_left n (LightMaskBits.time_bound L)
  have hs : n ≤ n*(L+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold LightMaskBitTable.time
  ring_nf at hm hs ⊢
  omega
end ThreeSum.LightLocalCoverCost
