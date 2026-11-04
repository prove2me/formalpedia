-- Prove2me | solution 1 for ThreeSum.WeightedPreparedBudget.rank_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:49:42.942264+00:00
-- url     : https://prove2.me/submissions/fbb2ceaa-1c08-4e8a-bae3-0847d3e8e779

import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_PreparedBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedPreparedBudget
theorem _root_.solution (N : ℕ) : LightWeightedCost.time N≤2000*(N+1)^2 := by
  unfold LightWeightedCost.time LightTernaryCodes.digitTime LightMaskErase.time
  nlinarith
end ThreeSum.WeightedPreparedBudget
