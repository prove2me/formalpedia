-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.sourceCap_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:21:06.316288+00:00
-- url     : https://prove2.me/submissions/2216989a-3911-4ce3-8095-a949a7f03a3c

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
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_endpoint_le_output
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_base_lower


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
theorem _root_.solution {K m : ℕ} (hK : 0<K) (hgood : GoodBlock K m) :
    (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m):ℝ)≤
      17*(nativePrime K m:ℝ)/(partitionCap m:ℝ) :=by
  let P:=nativePrime K m
  let V:=(TernaryCoverLocal.fieldVertices (fixedLength m) P (fixedAlpha m)).card
  have hpN : 0<P:=(nativePrime_prime K m).pos
  have hp : 0<(P:ℝ):=by exact_mod_cast hpN
  have hR : 0<(partitionCap m:ℝ) :=by unfold partitionCap; positivity
  have hRM : (partitionCap m:ℝ)≤P :=by exact_mod_cast WeightedGlobalOversizeDimensions.partition_le_native hK m
  have hV : V≤outputSize m :=by
    have hh : V≤endpointSize m:=Finset.card_image_le
    exact hh.trans (endpoint_le_output hK hgood)
  have hcap : WeightedGlobalCoverCapParameters.sourceCap m P*P≤8*(P+V)+P :=by
    unfold WeightedGlobalCoverCapParameters.sourceCap
    rw [Nat.ceilDiv_eq_add_pred_div]
    have hh:=Nat.div_mul_le_self (8*(P+V)+P-1) P
    change (8*(P+V)+P-1)/P*P≤_
    omega
  have hcapR : (WeightedGlobalCoverCapParameters.sourceCap m P:ℝ)*P≤9*(P:ℝ)+8*(outputSize m:ℝ) :=by
    have hc : (WeightedGlobalCoverCapParameters.sourceCap m P:ℝ)*P≤8*((P:ℝ)+V)+P :=by exact_mod_cast hcap
    have hv : (V:ℝ)≤outputSize m:=by exact_mod_cast hV
    linarith
  have hM : (outputSize m:ℝ)*(partitionCap m:ℝ)≤(P:ℝ)^2 :=by
    exact_mod_cast nativePrime_base_lower hK m
  have hprod:=mul_le_mul_of_nonneg_right hcapR hR.le
  have hpR:=mul_le_mul_of_nonneg_left hRM hp.le
  apply (le_div_iff₀ hR).mpr
  change (WeightedGlobalCoverCapParameters.sourceCap m P:ℝ)*(partitionCap m:ℝ)≤17*(P:ℝ)
  nlinarith only [hprod,hpR,hM,hp]
end ThreeSum.WeightedGlobalActualPrefixRuntime
