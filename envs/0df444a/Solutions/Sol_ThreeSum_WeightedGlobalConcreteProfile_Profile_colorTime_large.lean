-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.colorTime_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:01:39.282214+00:00
-- url     : https://prove2.me/submissions/5a2eb29d-61b5-4be1-bf0e-720af1198527

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_preparation_le_colorTime

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
theorem _root_.solution (P : Profile κ) (n : ℕ) : 10000≤P.colorTime n := by
  have hh := preparation_le_colorTime P n
  omega
end ThreeSum.WeightedGlobalConcreteProfile.Profile
