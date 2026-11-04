-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCountFrontendBudget.width_bound_from_logs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:21:54.910121+00:00
-- url     : https://prove2.me/submissions/a2f0bb79-305f-46e8-a00a-811dd39bfae1

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
theorem _root_.solution {m n j v : ℕ} (hj : j≤radixLength m n) (f g : Config)
    (hf : f.L≤2*fixedLength (j*m)) (hg : g.L≤2*fixedLength (j*m))
    (hv : Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)≤v*(radixLength m n+1)) :
    width (fixedLength (j*m)) f g≤(5*fixedLength m+v+3)*(radixLength m n+1) := by
  have hlen : fixedLength (j*m)=j*fixedLength m := by unfold fixedLength; ring
  have hN := Nat.mul_le_mul_right (fixedLength m) hj
  unfold width
  rw [hlen] at hf hg ⊢
  nlinarith only [hf,hg,hv,hN]
end ThreeSum.WeightedGlobalCountFrontendBudget
