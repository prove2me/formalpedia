-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime.bundle_bank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:30:55.808656+00:00
-- url     : https://prove2.me/submissions/69725acb-93de-4b4b-b31a-309ca40b751f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_ge_one


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime
theorem _root_.solution {K k b m n j : ℕ} (hfactor : 1≤nativeFactor K k b m) :
    (WeightedGlobalDimensionBounds.bankSize m j:ℝ)≤volumeBundle K k b m n j:=by
  have hpow : (1:ℝ)≤(nativeFactor K k b m:ℝ)^j:=one_le_pow₀ (by exact_mod_cast hfactor)
  have hh:=le_mul_of_one_le_left (Nat.cast_nonneg (WeightedGlobalDimensionBounds.bankSize m j)) hpow
  unfold volumeBundle
  have hE:=WeightedGlobalCountFrontendBudget.envelope_ge_one m j
  have hnon : 0≤(nativeFactor K k b m:ℝ)^j*((endpointSize m:ℝ)^j+
      (nativePrime K m:ℝ)^j+(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
        WeightedGlobalCountFrontendBudget.envelope m j):=by positivity
  nlinarith only [hh,hnon]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime
