-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.stageConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:06:54.046219+00:00
-- url     : https://prove2.me/submissions/1b7d1494-9d20-4a67-8f68-c4ca1d7efa56

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_volumeConstant_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_scoreConstant_nonneg

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
theorem _root_.solution (K k c d m F D E κ B : ℕ) :
    0≤stageConstant K k c d m F D E κ B:=by
  unfold stageConstant controllerConstant
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (scoreConstant_nonneg _ _ _ _ _ _ _ _ _))
      (mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonneg _ _ _ _ _))))
    (mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonneg _ _ _ _ _))
end ThreeSum.WeightedGlobalActualSeedRuntime
