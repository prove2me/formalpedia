-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:33:47.16298+00:00
-- url     : https://prove2.me/submissions/d7d988fe-426c-44c9-9353-405eb9223803

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_cut_schedule
import Theorems.Thm_ThreeSum_WeightedQueryBudget_actual_query_time_bound


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
theorem _root_.solution {m j L : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (LightWeightedFrozenQuery.queryTime L (bankCut m j) (fixedLength (j*m)) Q : ℝ)≤
      10000*((fixedLength (j*m) : ℝ)+L+1)*((fixedLength (j*m) : ℝ)+1)*envelope m j := by
  rw [envelope_eq_new,WeightedGlobalDimensionBounds.cut_schedule]
  exact WeightedQueryBudget.actual_query_time_bound Q hQ
end ThreeSum.WeightedGlobalCountFrontendBudget
