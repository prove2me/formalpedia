-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.exists_fixed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:32.019297+00:00
-- url     : https://prove2.me/submissions/6c1a031a-b892-43d4-bd8e-b91485a95a1d

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_principal_exponent_lt
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_common_fixed_block


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
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K) (c d minimum : ℕ) :
    ∃ m, minimum≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      principalExponent K (selectedMoment K) c d m<frontendExponent := by
  obtain ⟨m,hm,hgood,hover⟩ := common_fixed_block hK c d minimum
  exact ⟨m,hm,hgood,hover,principal_exponent_lt hK c d hgood hover⟩
end ThreeSum.WeightedGlobalCountFrontendBudget
