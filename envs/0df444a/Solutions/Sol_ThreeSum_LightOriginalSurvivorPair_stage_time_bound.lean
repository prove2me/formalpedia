-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.stage_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:51.338066+00:00
-- url     : https://prove2.me/submissions/89094287-b779-49a2-8aa7-333e9f9d47e7

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_time_bound
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le


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
theorem _root_.solution (keys : ℕ → ℕ) (n scanN L : ℕ) :
    LightOriginalSurvivorStage.time keys n scanN L ≤ 280*n+720+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by
  have h := LightOriginalCollisionCleanup.time_bound keys n scanN L
  have ht := length_le keys n
  unfold LightOriginalSurvivorStage.time LightReportingGather.time
  omega
end ThreeSum.LightOriginalSurvivorPair
