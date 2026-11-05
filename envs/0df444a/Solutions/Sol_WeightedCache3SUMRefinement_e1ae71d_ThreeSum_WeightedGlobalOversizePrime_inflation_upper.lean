-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime.inflation_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:34:59.284369+00:00
-- url     : https://prove2.me/submissions/0eef69c8-9258-4835-af49-26bcff92f17f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos

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
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) : inflation K m^K ≤ 2^K*outputSize m :=
  rootCeiling_upper hK (outputSize_pos m)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizePrime
