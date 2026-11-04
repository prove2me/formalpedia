-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.greedy_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:33.037737+00:00
-- url     : https://prove2.me/submissions/9814a8f8-0712-4dff-ab9d-6959bbf8ca60

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverCost
theorem _root_.solution (N C T : ℕ) :
    LightCoverGreedy.time N C T ≤ 1000*(N+1)*(C+1)*(T+1) := by
  unfold LightCoverGreedy.time LightCoverGreedy.roundTime LightCoverSelect.time
    LightCoverScores.time LightBooleanDot.time LightMinimum.time LightCoverUpdate.time fillTime
  ring_nf
  omega
end ThreeSum.LightLocalCoverCost
