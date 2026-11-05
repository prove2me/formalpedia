-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin.simultaneous_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:58:14.30366+00:00
-- url     : https://prove2.me/submissions/8781284c-e354-4c72-a0cb-81b97ce08324

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedFamilyMargin_family_fourth_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedParameters_simultaneous_parameters


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      WeightedGlobalSignedPadding.carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (family_fourth_eventually (by omega : 16<K) (selectedMoment K))
  obtain ⟨t,m,ht,hm,hg,ho,hc,hminor,hp⟩ :=
    WeightedGlobalSignedParameters.simultaneous_parameters hK hκ c d (max N N₀)
  exact ⟨t,m,ht,(le_max_left N N₀).trans hm,hg,ho,hc,hminor,hp,
    hN₀ m ((le_max_right N N₀).trans hm)⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
