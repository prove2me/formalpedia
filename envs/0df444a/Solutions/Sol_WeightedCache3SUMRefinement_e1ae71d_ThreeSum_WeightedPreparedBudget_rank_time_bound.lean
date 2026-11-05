-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.rank_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:02:45.66028+00:00
-- url     : https://prove2.me/submissions/58f920e7-dc49-4682-8fae-94382592eca3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget
theorem _root_.solution (N : ℕ) : LightWeightedCost.time N≤2000*(N+1)^2 := by
  unfold LightWeightedCost.time LightTernaryCodes.digitTime LightMaskErase.time
  nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget
