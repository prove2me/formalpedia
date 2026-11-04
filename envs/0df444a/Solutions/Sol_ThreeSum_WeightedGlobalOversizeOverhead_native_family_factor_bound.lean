-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.native_family_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:33.875897+00:00
-- url     : https://prove2.me/submissions/70687b07-b66d-4ba0-aa76-a3f7da36ef11

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_native_family_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution (K k c d m b : ℕ)
    (hb : b ≤ c*(fixedLength m+1)^d) :
    b*(nativeFamily K m k).length*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
        (inflation K m)^4*baseFactor K k c d m := by
  have hc : b ≤ (max 1 c)*(fixedLength m+1)^d :=
    hb.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
  have h := Nat.mul_le_mul_right
    ((nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) hc
  rw [native_family_length] at h
  rw [native_family_length]
  unfold inflatedFrequency baseFactor baseFrequency at *
  convert h using 1 <;> ring
end ThreeSum.WeightedGlobalOversizeOverhead
