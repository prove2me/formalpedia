-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedCollisionRate.simultaneous_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:31:38.609982+00:00
-- url     : https://prove2.me/submissions/d0654eb0-541d-4df6-a97f-1122fa32ea5c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_charge_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_simultaneous_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_native_large_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedCollisionRate
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      WeightedGlobalOversizeOverhead.overheadCharge (WeightedGlobalOversizeOverhead.selectedMoment K) c d m<
        WeightedGlobalOversizeOverhead.microAllowance K ∧
      WeightedGlobalSignedPadding.carryExponent m (2^t) κ<WeightedGlobalOversizeOverhead.microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (WeightedGlobalOversizeOverhead.selectedMoment K)).length)^4≤outputSize m ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by
  have hk : 0<K := by omega
  have hh : ∀ᶠ m : ℕ in atTop, 9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by
    filter_upwards [WeightedGlobalSignedParameters.native_large_eventually hk 9,charge_eventually hk] with m hp hc
    exact ⟨hp,hc⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hh
  obtain ⟨t,m,ht,hm,hg,ho,hc,hminor,hp,hF⟩ :=
    WeightedGlobalPairedFamilyMargin.simultaneous_parameters hK hκ c d (max N N₀)
  exact ⟨t,m,ht,(le_max_left N N₀).trans hm,hg,ho,hc,hminor,hp,hF,
    hN₀ m ((le_max_right N N₀).trans hm)⟩
end ThreeSum.WeightedGlobalPairedCollisionRate
