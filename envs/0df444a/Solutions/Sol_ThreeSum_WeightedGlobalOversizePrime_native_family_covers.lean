-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.native_family_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:35.426495+00:00
-- url     : https://prove2.me/submissions/8e56e929-3422-4388-a4eb-fed85bb3df8d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_base_lower
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_gt_four
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflated_frequency_scale
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativeCatalog_complete
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_actual_pruning_guard
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_sourceCap_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_greedy_covers
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K m k : ℕ} (hK : 0 < K) (hm : 0 < m) (hk : 0 < k)
    (t : ZMod (nativePrime K m) × ZMod (nativePrime K m)) :
    ∃ w ∈ nativeFamily K m k, Covers m (nativePrime K m) (sourceCap m (nativePrime K m))
      (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) w t := by
  have hF : 1 < inflatedFrequency K m := by
    have hi : 1 ≤ inflation K m^4 := Nat.one_le_pow _ _ (inflation_pos hK m)
    have h := Nat.mul_le_mul_left (frequencyFactor m) hi
    exact (frequencyFactor_gt_one m).trans_le (by simpa [inflatedFrequency] using h)
  exact greedy_covers m (nativePrime K m) (nativeCatalog K m) (nativeCatalog_complete K m)
    (nativePrime_gt_four hK hm) (nativePrime_base_lower hK m)
    (sourceCap m (nativePrime K m)) k
    (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)
    (inflatedFrequency K m) hF (rawThreshold_pos _ _ _) (sourceCap_threshold _ _ (nativePrime_prime K m).pos)
    (actual_pruning_guard _ _ _ _ hk) (inflated_frequency_scale hK m) t
end ThreeSum.WeightedGlobalOversizePrime
