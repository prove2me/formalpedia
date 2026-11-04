-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.local_factor_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:37:27.44542+00:00
-- url     : https://prove2.me/submissions/28c57dfe-57bb-434b-b1c4-90916b248f45

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
theorem _root_.solution (m : ℕ) : localFactor m≤19*(fixedLength m+1)^3 :=by
  have h1 : 2*(2380004124000*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have h2 : 3*(292746547000*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have h3 : 2*(292746547000*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have hh:=Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hpow : 1≤(fixedLength m+1)^3:=Nat.one_le_pow _ _ (by omega)
  unfold localFactor WeightedGlobalPartitionCount.partitionLoss
  nlinarith only [hh,hpow]
end ThreeSum.WeightedGlobalActualPrefixRuntime
