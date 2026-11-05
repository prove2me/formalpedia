-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime.endpoint_le_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:40:59.96662+00:00
-- url     : https://prove2.me/submissions/e91d5b74-0b7c-4176-86bf-f8cada82a7d5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_endpoint_count
import Theorems.Thm_ThreeSum_TernaryEntropyRates_typeCount_pos
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_endpoint_charge_eq
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_output_log_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_actual_endpoint_count
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_typeCount_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_endpoint_charge_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_endpoint_charge_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime
theorem _root_.solution {K m : ℕ} (hK : 0<K) (hgood : GoodBlock K m) :
    endpointSize m≤outputSize m :=by
  have hm:=hgood.1
  have hMp : 0<(outputSize m:ℝ) :=by exact_mod_cast WeightedGlobalOversizePrime.outputSize_pos m
  have hEp : 0<(endpointSize m:ℝ) :=by
    have hh : 0<endpointSize m :=by rw [actual_endpoint_count]; exact typeCount_pos (by decide) m
    exact_mod_cast hh
  have hS : 0≤Real.log (inflation K m:ℝ) :=Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hc : WeightedGlobalOversizeRates.endpointCharge K m<2 :=by
    have hh:=hgood.2.2.2.1
    norm_num [softCertificate] at hh ⊢
    linarith
  rw [←WeightedGlobalOversizeDimensions.endpoint_charge_eq hm] at hc
  have hl:= (div_lt_iff₀ (WeightedGlobalPrincipalDimensions.output_log_pos hm)).mp hc
  unfold WeightedGlobalOversizeDimensions.tableSlope at hl
  have he : Real.log (endpointSize m:ℝ)≤Real.log (outputSize m:ℝ) :=by linarith
  exact_mod_cast (Real.log_le_log_iff hEp hMp).mp he
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime
