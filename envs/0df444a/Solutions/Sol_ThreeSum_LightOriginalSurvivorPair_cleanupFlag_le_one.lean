-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.cleanupFlag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:22.326207+00:00
-- url     : https://prove2.me/submissions/19c0af80-f11d-4ac1-b7ea-339d09930fdd

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_le_one
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_le_one


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightOriginalSurvivorPair
theorem _root_.solution (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    cleanupFlag A B C keysB keysC nA nB nC ≤ 1 := by
  unfold cleanupFlag
  split
  · exact LightDeletedTwoSum.flag_le_one _ _ _ _ _ _ _ _
  · omega
end ThreeSum.LightOriginalSurvivorPair
