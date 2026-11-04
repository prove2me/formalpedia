-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.rootCeiling_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:02.018206+00:00
-- url     : https://prove2.me/submissions/8bd520db-97e4-4299-a73f-8ab60216a8c4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCandidates_nonempty

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M ∈ rootCandidates K M := by
  rw [rootCeiling,dif_pos (rootCandidates_nonempty hK hM)]
  exact min'_mem _ _
end ThreeSum.WeightedGlobalOversizePrime
