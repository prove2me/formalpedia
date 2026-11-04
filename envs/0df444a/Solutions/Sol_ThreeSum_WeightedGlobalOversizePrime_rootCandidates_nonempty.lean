-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.rootCandidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:03:35.337868+00:00
-- url     : https://prove2.me/submissions/866c69ad-23e9-42cf-aeb4-ee7475f3c8b4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    (rootCandidates K M).Nonempty := by
  refine ⟨M,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
  exact Nat.le_self_pow hK.ne' M
end ThreeSum.WeightedGlobalOversizePrime
