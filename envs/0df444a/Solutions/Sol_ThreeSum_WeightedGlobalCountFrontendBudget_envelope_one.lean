-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.envelope_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:31:59.074692+00:00
-- url     : https://prove2.me/submissions/841aee33-5368-41e3-a996-0baa11a1b0de

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
import Theorems.Thm_ThreeSum_WeightedQueryBudget_envelope_one


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
theorem _root_.solution {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) : 1≤envelope m j := by
  rw [envelope_eq_new]
  exact WeightedQueryBudget.envelope_one Q hQ
end ThreeSum.WeightedGlobalCountFrontendBudget
