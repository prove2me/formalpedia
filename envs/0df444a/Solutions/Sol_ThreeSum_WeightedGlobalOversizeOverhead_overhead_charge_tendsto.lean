-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.overhead_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:04.603602+00:00
-- url     : https://prove2.me/submissions/8dcf4f98-3dcb-4af6-b884-ace77b10bae1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_rateUpper_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {k : ℕ} (hk : 0 < k) (c d : ℕ) :
    Tendsto (overheadCharge k c d) atTop (𝓝 (40/((k : ℝ)*Hpi))) := by
  have h := ((rateUpper_tendsto hk c d).const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · ring
end ThreeSum.WeightedGlobalOversizeOverhead
