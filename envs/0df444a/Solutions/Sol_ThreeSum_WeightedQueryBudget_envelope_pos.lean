-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.envelope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:50:21.711664+00:00
-- url     : https://prove2.me/submissions/7a16944f-a463-44fc-9d29-5e37f06e98f5

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedQueryBudget
theorem _root_.solution (m : ℕ) : 0<envelope m := div_pos (exp_pos _) (pow_pos z_pos _)
end ThreeSum.WeightedQueryBudget
