-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.fast_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:17:05.036128+00:00
-- url     : https://prove2.me/submissions/795a7318-4815-4b1d-961f-0ab0d529f942

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_color_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramBudget_full


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalConcreteProfile ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light StageBounds WeightedGlobalLocalParameters WeightedGlobalActualColoredRuntime
open WeightedGlobalActualPrefixRuntime WeightedGlobalOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalConcreteProfile.Profile
theorem _root_.solution (P : Profile κ) : PowerBound P.fastTime exponent :=
  WeightedGlobalFastProgramBudget.full P.blockPositive P.radix_gt_one P.color_powerBound
    (by norm_num [exponent])
end ThreeSum.WeightedGlobalConcreteProfile.Profile
