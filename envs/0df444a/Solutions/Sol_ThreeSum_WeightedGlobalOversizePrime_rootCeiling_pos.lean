-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.rootCeiling_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:11.780964+00:00
-- url     : https://prove2.me/submissions/bc8ac07b-626d-4377-95ca-ea5106a20021

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_lower

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    0 < rootCeiling K M := by
  have h := rootCeiling_lower hK hM
  by_contra hn
  have hz : rootCeiling K M=0 := by omega
  rw [hz,zero_pow hK.ne'] at h
  omega
end ThreeSum.WeightedGlobalOversizePrime
