-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.outputSize_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:48.112749+00:00
-- url     : https://prove2.me/submissions/8de79e6f-57ed-47df-aa3d-7612a63a88b2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_count
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_typeCount_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution (m : ℕ) : 0 < outputSize m := by
  rw [actual_output_count]
  exact typeCount_pos (by decide) m
end ThreeSum.WeightedGlobalOversizePrime
