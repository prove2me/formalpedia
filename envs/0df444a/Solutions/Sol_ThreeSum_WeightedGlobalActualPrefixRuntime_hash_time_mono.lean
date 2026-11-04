-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.hash_time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:10:24.290041+00:00
-- url     : https://prove2.me/submissions/6210d82d-4102-4286-bec6-75fc66824d93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualPrefixRuntime
theorem _root_.solution (J p b B : ℕ) (h : b≤B) :
    LightSignedRowHash.time J p b≤LightSignedRowHash.time J p B :=by
  unfold LightSignedRowHash.time LightNaturalDot.reducedTime
  gcongr
end ThreeSum.WeightedGlobalActualPrefixRuntime
