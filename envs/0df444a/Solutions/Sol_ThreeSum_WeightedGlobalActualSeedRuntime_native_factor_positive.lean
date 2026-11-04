-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.native_factor_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:19:55.539603+00:00
-- url     : https://prove2.me/submissions/de18cc37-5152-466f-a099-5d6ecf79d020

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos


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
theorem _root_.solution {K k b m F : ℕ} (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b) : 1≤nativeFactor K k b m:=by
  have hb' : 0<b:=by unfold WeightedGlobalActualPrefixRuntime.localFactor at hb; omega
  have hfamily : 0<(nativeFamily K m k).length:=lt_of_lt_of_le hFpos hF
  unfold nativeFactor
  exact Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.mul_pos hb' hfamily)
    (WeightedGlobalCoverCapParameters.rawThreshold_pos _ _ _))
end ThreeSum.WeightedGlobalActualSeedRuntime
