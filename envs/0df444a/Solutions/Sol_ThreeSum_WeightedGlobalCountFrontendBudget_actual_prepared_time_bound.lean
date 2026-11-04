-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.actual_prepared_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:45:20.878803+00:00
-- url     : https://prove2.me/submissions/bb4785b7-8d74-4581-b3d2-f61a809183e5

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_cut_schedule
import Theorems.Thm_ThreeSum_WeightedPreparedBudget_actual_prepared_time_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution {m j : ℕ} (f g : Config)
    (hT : f.T=bankCut m j) (Q : TritWord (fixedLength (j*m))) (hQ : HasType Q (fixedPi (j*m))) :
    (LightWeightedPreparedWanted.time f g Q : ℝ)≤
      100000*(width (fixedLength (j*m)) f g : ℝ)^3*envelope m j := by
  rw [envelope_eq_new]
  exact WeightedPreparedBudget.actual_prepared_time_bound f g
    (hT.trans (WeightedGlobalDimensionBounds.cut_schedule m j)) Q hQ
end ThreeSum.WeightedGlobalCountFrontendBudget
