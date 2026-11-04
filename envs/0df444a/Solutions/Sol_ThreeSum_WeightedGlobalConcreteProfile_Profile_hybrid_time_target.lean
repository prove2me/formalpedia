-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.hybrid_time_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:41:36.154934+00:00
-- url     : https://prove2.me/submissions/de9b03b2-52ca-4e46-be1c-efd0d46b8629

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_fast_powerBound
import Theorems.Thm_ThreeSum_TernaryHybridCosts_timeUpTo_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff


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
theorem _root_.solution (P : Profile κ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo P.hybridTime n ((n:ℝ)^(κ:ℝ))≤(n:ℝ)^(96013971/50000000:ℝ) :=
  TernaryHybridCosts.timeUpTo_eventually P.fast_powerBound
    (by norm_num [exponent]) (by norm_num [exponent]) κ P.cutoff
end ThreeSum.WeightedGlobalConcreteProfile.Profile
