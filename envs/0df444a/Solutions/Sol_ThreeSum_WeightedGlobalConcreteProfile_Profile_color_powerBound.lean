-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.color_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:47:31.731767+00:00
-- url     : https://prove2.me/submissions/a01d3349-98a7-46af-838f-9f4b2b62c5b3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_PB
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_selected_room
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_PB


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
theorem _root_.solution (P : Profile κ) : PowerBound P.colorTime exponent := by
  have hδ : 0≤microAllowance P.K := by unfold microAllowance; positivity
  have hroom := (selected_room P.large).le
  exact WeightedGlobalActualGlobalQueryRuntime.PB
    P.blockPositive P.radix_gt_one hδ P.carry hroom
end ThreeSum.WeightedGlobalConcreteProfile.Profile
