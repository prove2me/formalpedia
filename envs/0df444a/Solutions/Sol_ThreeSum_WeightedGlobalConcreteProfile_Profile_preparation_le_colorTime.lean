-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.preparation_le_colorTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:46:18.149132+00:00
-- url     : https://prove2.me/submissions/c6dabf68-c069-4dcf-86b6-f1a7e4cab398

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime

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
theorem _root_.solution (P : Profile κ) (n : ℕ) :
    LightWeightedGlobalColorPreparationProof.time n
      (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ)) (n^κ)+
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+10000≤
        P.colorTime n := by
  unfold colorTime WeightedGlobalActualGlobalQueryRuntime.uniformTime WeightedGlobalActualColoredRuntime.uniformTime
  change _≤LightWeightedGlobalColorPreparationProof.time n
    (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ)) (n^κ)+_+_+_+10000+_
  omega
end ThreeSum.WeightedGlobalConcreteProfile.Profile
