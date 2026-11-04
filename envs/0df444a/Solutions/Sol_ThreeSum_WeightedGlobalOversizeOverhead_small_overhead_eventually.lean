-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.small_overhead_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:51.056692+00:00
-- url     : https://prove2.me/submissions/e7125457-6286-4ddc-887d-34b2d3173196

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_overhead_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_selectedMoment_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_moment_limit_lt_allowance

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 0 < K) (c d : ℕ) :
    ∀ᶠ m : ℕ in atTop, overheadCharge (selectedMoment K) c d m < microAllowance K :=
  (overhead_charge_tendsto (selectedMoment_pos hK) c d).eventually
    (gt_mem_nhds (moment_limit_lt_allowance hK))
end ThreeSum.WeightedGlobalOversizeOverhead
