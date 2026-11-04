-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.y_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:45:58.426605+00:00
-- url     : https://prove2.me/submissions/099cf1fb-9ea5-43ff-b286-baa1f2838799

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedQueryBudget
theorem _root_.solution : 0<yRoot := by norm_num [yRoot]
end ThreeSum.WeightedQueryBudget
