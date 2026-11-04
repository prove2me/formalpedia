-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFixedParameters.familyLength_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:08:53.085998+00:00
-- url     : https://prove2.me/submissions/9e9f7479-281a-40eb-8281-8077a29ee464

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_native_family_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaFixedParameters
theorem _root_.solution {K : ℕ} (hK : 0<K) (m : ℕ) : 0<familyLength K m := by
  unfold familyLength
  rw [native_family_length]
  unfold inflatedFrequency
  have hf := WeightedGlobalCoverCapParameters.frequencyFactor_gt_one m
  have hs := inflation_pos hK m
  positivity
end ThreeSum.WeightedGlobalArenaFixedParameters
