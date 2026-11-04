-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.volumeConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:19:31.203476+00:00
-- url     : https://prove2.me/submissions/8c93c140-cc2b-43e2-a86c-31de8ca48c29

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_gibbs_parameters


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
theorem _root_.solution (K k c d m : ℕ) : 0≤volumeConstant K k c d m:=by
  unfold volumeConstant
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  exact add_nonneg (add_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le)
    (div_nonneg (Real.exp_pos _).le (pow_pos WeightedGlobalParameters.gibbs_parameters.2.2.1 1024).le)
end ThreeSum.WeightedGlobalActualSeedRuntime
