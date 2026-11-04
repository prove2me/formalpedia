-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.paired_drift_with_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:26.895311+00:00
-- url     : https://prove2.me/submissions/438805f0-b9b0-404b-82f1-3c48e8c8e00a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 100 ≤ K) :
    -1/(K : ℝ)+8/(K : ℝ)^2+20*(K : ℝ)*microAllowance K < 0 := by
  have hk : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (0 : ℝ) < K := by linarith
  unfold microAllowance
  field_simp [hp.ne']
  nlinarith
end ThreeSum.WeightedGlobalOversizeOverhead
