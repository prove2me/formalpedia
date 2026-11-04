-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.rootCeiling_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:13.574935+00:00
-- url     : https://prove2.me/submissions/166f1820-78ba-414a-8351-df9693ac5390

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_mem

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M ≤ M := by
  have h := (mem_range.mp (mem_filter.mp (rootCeiling_mem hK hM)).1)
  omega
end ThreeSum.WeightedGlobalOversizePrime
