-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget.y_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:02:01.505025+00:00
-- url     : https://prove2.me/submissions/850b5c48-1d3e-4742-8e61-eb78d914ef57

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters_e1ae71d
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
theorem _root_.solution : yRoot<1 := by norm_num [yRoot]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
