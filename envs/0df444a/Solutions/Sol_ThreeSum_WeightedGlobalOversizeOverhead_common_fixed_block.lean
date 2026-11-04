-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.common_fixed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:58:11.993386+00:00
-- url     : https://prove2.me/submissions/66a86390-de9b-4b01-9eb3-913de31b681a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_small_overhead_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_goodBlock_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_goodBlock_eventually


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000 ≤ K) (c d N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m < microAllowance K := by
  have hk : 0 < K := by omega
  have h : ∀ᶠ m : ℕ in atTop, N ≤ m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m < microAllowance K := by
    filter_upwards [eventually_ge_atTop N,goodBlock_eventually hK,small_overhead_eventually hk c d] with m hm hg ho
    exact ⟨hm,hg,ho⟩
  exact h.exists
end ThreeSum.WeightedGlobalOversizeOverhead
