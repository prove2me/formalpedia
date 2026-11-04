-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.z_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:45:57.072723+00:00
-- url     : https://prove2.me/submissions/bbe60fb5-10bd-423d-a886-1a877aae802c

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
theorem _root_.solution : 0<zRoot := by norm_num [zRoot]
end ThreeSum.WeightedQueryBudget
