-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.inflation_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:35.323358+00:00
-- url     : https://prove2.me/submissions/d8ee0c6f-6dc9-4ac1-b0cd-6250163ca782

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) : 0 < inflation K m :=
  rootCeiling_pos hK (outputSize_pos m)
end ThreeSum.WeightedGlobalOversizePrime
