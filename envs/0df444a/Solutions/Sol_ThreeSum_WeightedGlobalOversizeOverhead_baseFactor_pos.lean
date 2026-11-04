-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.baseFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:03:50.281346+00:00
-- url     : https://prove2.me/submissions/60b921f9-f66e-4e95-a368-5a59c37e9c67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution (K k c d m : ℕ) : 0 < baseFactor K k c d m := by
  have hc : 0 < max 1 c := lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)
  have hF := frequencyFactor_gt_one m
  have hτ := rawThreshold_pos (nativePrime K m) (sourceCap m (nativePrime K m)) k
  unfold baseFactor baseFrequency
  positivity
end ThreeSum.WeightedGlobalOversizeOverhead
