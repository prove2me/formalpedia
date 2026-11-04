-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.inflation_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:35.846479+00:00
-- url     : https://prove2.me/submissions/9d43657f-77b4-4c73-a6aa-9c317e15ed22

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_upper
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) : inflation K m^K ≤ 2^K*outputSize m :=
  rootCeiling_upper hK (outputSize_pos m)
end ThreeSum.WeightedGlobalOversizePrime
