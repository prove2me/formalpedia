-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.moment_limit_lt_allowance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:44.357372+00:00
-- url     : https://prove2.me/submissions/66548fcb-bad0-4796-8446-84315f0160c4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 0 < K) :
    40/((selectedMoment K : ℝ)*Hpi) < microAllowance K := by
  have hkR : (0 : ℝ) < K := by exact_mod_cast hK
  have hH : (4/5 : ℝ) < Hpi := by linarith [Hpi_bounds.1]
  unfold selectedMoment microAllowance
  push_cast
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_pos (sq_pos_of_pos hkR) (sub_pos.mpr hH)]
end ThreeSum.WeightedGlobalOversizeOverhead
