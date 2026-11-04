-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.bundle_bank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:20:54.921628+00:00
-- url     : https://prove2.me/submissions/16b9430d-6ca2-4569-a834-4431df64595b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_ge_one


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
end ThreeSum.WeightedGlobalActualSeedRuntime
