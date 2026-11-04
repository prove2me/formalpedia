-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.inflation_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:38.987386+00:00
-- url     : https://prove2.me/submissions/8b369db0-0e6e-477c-8699-e9ad1fdca6ef

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_lower
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) : outputSize m ≤ inflation K m^K :=
  rootCeiling_lower hK (outputSize_pos m)
end ThreeSum.WeightedGlobalOversizePrime
