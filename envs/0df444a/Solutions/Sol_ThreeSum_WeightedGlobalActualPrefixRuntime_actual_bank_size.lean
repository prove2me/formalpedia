-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.actual_bank_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:12:01.61419+00:00
-- url     : https://prove2.me/submissions/77bed56f-5ffb-457f-9e25-30b414ac7f26

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
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card


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
theorem _root_.solution (m r : ℕ) : nb m r=bankSize m r :=by
  unfold nb bankCodes
  rw [WeightedBankEnumeration.codes_length_eq_bank_card]
  have hn : N m r=fixedLength (r*m):=by unfold N fixedLength; ring
  have ht : cut m r=bankCut m r:=by unfold cut bankCut LightWeightedGlobalPrefixSetup.T; ring
  rw [hn,ht]
  rfl
end ThreeSum.WeightedGlobalActualPrefixRuntime
