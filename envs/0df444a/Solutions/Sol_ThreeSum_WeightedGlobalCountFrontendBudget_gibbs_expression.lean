-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.gibbs_expression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:23.461462+00:00
-- url     : https://prove2.me/submissions/2fd2abf6-6ba9-4a3e-bff2-8a4b975c5c87

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_deficit_schedule
import Theorems.Thm_ThreeSum_WeightedQueryBudget_gibbs_expression


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
    (hQ : HasType Q (fixedPi (j*m))) :
    queryArg1^digitCount Q 1*queryArg2^digitCount Q 2/z^queryDeficit m j=envelope m j := by
  rw [envelope_eq_new,WeightedGlobalDimensionBounds.deficit_schedule]
  exact WeightedQueryBudget.gibbs_expression Q hQ
end ThreeSum.WeightedGlobalCountFrontendBudget
