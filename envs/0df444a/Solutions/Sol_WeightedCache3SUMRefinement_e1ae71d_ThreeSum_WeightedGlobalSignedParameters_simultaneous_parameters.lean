-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters.simultaneous_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:49:19.175984+00:00
-- url     : https://prove2.me/submissions/1de8569a-5c5e-4d0e-81b3-86da5adb2754

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedParameters_native_large_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedParameters_padding_slope_tendsto_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedParameters_power_two_base
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_goodBlock_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_small_overhead_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_goodBlock_eventually


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m := by
  have hk : 0<K := by omega
  have hδ : 0<microAllowance K := by unfold microAllowance; positivity
  obtain ⟨t,ht,hbase,hslope⟩ := power_two_base hκ hδ
  have hpadd := padding_slope_tendsto_zero.eventually
    (gt_mem_nhds (half_pos hδ))
  have h : ∀ᶠ m : ℕ in atTop, N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧ 2*(2^t)<nativePrime K m := by
    filter_upwards [eventually_ge_atTop N,goodBlock_eventually hK,
      small_overhead_eventually hk c d,hpadd,
      native_large_eventually hk ((2*K).factorial*(2^t)^(2*K)),
      native_large_eventually hk (2*(2^t))] with m hN hg ho hpad hminor hp
    refine ⟨hN,hg,ho,?_,hminor,hp⟩
    unfold carryExponent
    linarith only [hslope,hpad]
  obtain ⟨m,hm⟩ := h.exists
  exact ⟨t,m,ht,hm⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
