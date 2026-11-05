-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead.selectedMoment_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:12:12.790859+00:00
-- url     : https://prove2.me/submissions/957f3711-9d40-475e-822b-d462ce35ad38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 0 < K) : 0 < selectedMoment K := by
  unfold selectedMoment
  positivity
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
