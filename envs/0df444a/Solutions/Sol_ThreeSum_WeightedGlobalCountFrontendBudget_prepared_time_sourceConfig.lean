-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:29.353597+00:00
-- url     : https://prove2.me/submissions/cec38d8e-7e51-4977-9f6b-77e1b2ee6f12

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
theorem _root_.solution {N : ℕ} (f g : Config) (Q : TritWord N)
    (fbase gbase stride tail group : ℕ) :
    LightWeightedPreparedWanted.time
      (LightWeightedWantedRowDispatch.sourceConfig f fbase stride tail group)
      (LightWeightedWantedRowDispatch.sourceConfig g gbase stride tail group) Q=
      LightWeightedPreparedWanted.time f g Q := rfl
end ThreeSum.WeightedGlobalCountFrontendBudget
