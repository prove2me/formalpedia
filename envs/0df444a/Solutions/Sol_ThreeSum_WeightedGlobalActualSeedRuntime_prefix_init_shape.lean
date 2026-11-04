-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.prefix_init_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:21:16.744314+00:00
-- url     : https://prove2.me/submissions/aed120b3-14c6-43c3-8201-df578ac6f67d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualSeedRuntime
theorem _root_.solution (C : LightWeightedGlobalSeedScoreFactory.Config) (rounds T : ℕ) :
    LightWeightedGlobalPrefixInit.time C rounds T≤
      (rounds+1)*(T+10000*(C.nB+C.nC+C.nO+C.J+1)):=by
  unfold LightWeightedGlobalPrefixInit.time LightTernaryInitialKeys.time LightWeightedGlobalPrefixLoop.time copyTime fillTime
  ring_nf
  omega
end ThreeSum.WeightedGlobalActualSeedRuntime
