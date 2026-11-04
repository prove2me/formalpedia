-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:07.160857+00:00
-- url     : https://prove2.me/submissions/b5f855f6-2fc5-40a2-ae61-a1dd0dd63706

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_stage_time_bound

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
theorem _root_.solution (keysB keysC : ℕ → ℕ) (nA nB nC L : ℕ) :
    time keysB keysC nA nB nC L ≤ 280*(nB+nC)+1640+
      ((TernaryOriginalCollisions.collisionPairs (fun i : Fin nB => keysB i.val)).card+
       (TernaryOriginalCollisions.collisionPairs (fun i : Fin nC => keysC i.val)).card)*
        (nA*(120*L+330)+300) := by
  have hb := stage_time_bound keysB nB nA L
  have hc := stage_time_bound keysC nC nA L
  unfold time
  rw [Nat.add_mul]
  omega
end ThreeSum.LightOriginalSurvivorPair
