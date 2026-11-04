-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualCleanupRuntime.stage_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:29:05.037865+00:00
-- url     : https://prove2.me/submissions/88feb57a-2623-40ae-9501-5430823366a1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_bad_length_le_collisions
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_length_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalActualCleanupRuntime
theorem _root_.solution (keys : ℕ→ℕ) (size scan L n : ℕ) (hs : size≤n) (hscan : scan≤n) :
    LightOriginalSurvivorStage.time keys size scan L≤
      280*n+720+collisions keys size*(n*(120*L+330)+300) := by
  have hbad:=LightOriginalCollisionCleanup.bad_length_le_collisions keys size
  have hsurv:=(LightOriginalSurvivors.length_le keys size).trans hs
  have hcost : scan*(120*L+330)+300≤n*(120*L+330)+300 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ hscan) _
  have hm:=Nat.mul_le_mul hbad hcost
  unfold LightOriginalSurvivorStage.time LightOriginalCollisionCleanup.time
    LightOriginalBucketFilter.time LightDeletedTwoSum.time LightColoredTwoSum.time
    LightBandLookup.time LightBandLookup.searchTime LightReportingGather.time
  change _≤280*n+720+collisions keys size*(n*(120*L+330)+300)
  change (LightOriginalCollisionCleanup.badIndices keys size).length*
    (scan*(120*L+330)+300)≤collisions keys size*(n*(120*L+330)+300) at hm
  nlinarith only [hm,hs,hsurv]
end ThreeSum.WeightedGlobalActualCleanupRuntime
