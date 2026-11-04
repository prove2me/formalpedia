-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.extraCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:10:46.746204+00:00
-- url     : https://prove2.me/submissions/36c7a720-1b75-4e81-a022-d95ddbf1a11b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_volumeConstant_nonneg


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualGlobalQueryRuntime
theorem _root_.solution (K k c d m F D E κ B H : ℕ) :
    0≤extraCoefficient K k c d m F D E κ B H:=by
  unfold extraCoefficient
  positivity [volumeConstant_nonneg K k c d m]
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
