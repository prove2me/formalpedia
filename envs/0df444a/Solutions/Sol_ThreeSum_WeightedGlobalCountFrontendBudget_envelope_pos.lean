-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.envelope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:07.353751+00:00
-- url     : https://prove2.me/submissions/8e3a7dc8-542b-4bc1-8816-0824254baea0

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
import Theorems.Thm_ThreeSum_WeightedQueryBudget_envelope_pos


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
theorem _root_.solution (m j : ℕ) : 0<envelope m j := by
  rw [envelope_eq_new]
  exact WeightedQueryBudget.envelope_pos _
end ThreeSum.WeightedGlobalCountFrontendBudget
