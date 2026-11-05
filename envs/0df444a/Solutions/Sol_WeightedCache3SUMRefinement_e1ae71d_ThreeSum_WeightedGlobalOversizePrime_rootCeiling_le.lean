-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime.rootCeiling_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:30:12.621656+00:00
-- url     : https://prove2.me/submissions/594c674a-c268-4820-85ca-be8fdddbf0ce

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_mem

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M ≤ M := by
  have h := (mem_range.mp (mem_filter.mp (rootCeiling_mem hK hM)).1)
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime
