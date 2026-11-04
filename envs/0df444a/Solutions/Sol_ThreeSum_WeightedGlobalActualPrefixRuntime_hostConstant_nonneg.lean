-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.hostConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:26:52.243233+00:00
-- url     : https://prove2.me/submissions/bc75ce65-3865-4124-92ea-826525d978ea

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
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_gibbs_parameters


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
theorem _root_.solution (K k c d m F D E κ : ℕ) : 0≤hostConstant K k c d m F D E κ:=by
  unfold hostConstant
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold volumeConstant
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  exact add_nonneg (add_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le)
    (div_nonneg (Real.exp_pos _).le (pow_pos WeightedGlobalParameters.gibbs_parameters.2.2.1 1024).le)
end ThreeSum.WeightedGlobalActualPrefixRuntime
