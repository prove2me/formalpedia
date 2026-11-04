-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.envelope_eq_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:16:56.742025+00:00
-- url     : https://prove2.me/submissions/d3c1274a-7baf-43d7-af48-509abc92c042

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget

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
theorem _root_.solution (m j : ℕ) : envelope m j=WeightedQueryBudget.envelope (j*m) := by
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (fixedLength (j*m) : ℝ)*WeightedCacheParameters.Qn := by
    unfold queryEntropy
    field_simp
  unfold envelope
  rw [he]
  rfl
end ThreeSum.WeightedGlobalCountFrontendBudget
