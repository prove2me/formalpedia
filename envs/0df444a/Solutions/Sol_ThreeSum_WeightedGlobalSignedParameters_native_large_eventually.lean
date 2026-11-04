-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedParameters.native_large_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:43:13.225211+00:00
-- url     : https://prove2.me/submissions/1864fe71-8a83-4d12-b89c-c9bfb6a91670

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_native_log_atTop

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedParameters
theorem _root_.solution {K : ℕ} (hK : 0<K) (D : ℕ) :
    ∀ᶠ m : ℕ in atTop, D<nativePrime K m := by
  filter_upwards [(native_log_atTop hK).eventually_gt_atTop (D : ℝ)] with m hm
  have hlog := Real.log_le_self (Nat.cast_nonneg (nativePrime K m) : (0 : ℝ)≤_)
  exact_mod_cast hm.trans_le hlog
end ThreeSum.WeightedGlobalSignedParameters
