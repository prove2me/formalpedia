-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedSelectedChain.actual_good_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:54:29.0542+00:00
-- url     : https://prove2.me/submissions/f651401d-528a-4f27-829c-72236d4bbf6c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryPairedRecurrence_scaled_step_iff
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
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
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
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
open ThreeSum ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedSelectedChain
theorem _root_.solution (a b p oldPi nextPi oldB nextB oldC nextC sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext)
    (flag vPi vB vC : ℕ→ℤ) (chosen : ℕ)
    (hPi : vPi chosen=(sNext*nextPi : ℕ))
    (hB : vB chosen=(nextB : ℕ)) (hC : vC chosen=(nextC : ℕ))
    (hgood : LightTernaryRowSelector.Good flag vPi vB vC (a*sOld) p p
      (b*sNext*(sOld*oldPi)) (9*oldB) (9*oldC) chosen) :
    a*nextPi≤b*oldPi ∧ p*nextB≤9*oldB ∧ p*nextC≤9*oldC := by
  rcases hgood with ⟨_,h0,h1,h2⟩
  rw [hPi] at h0
  rw [hB] at h1
  rw [hC] at h2
  have h0N' : (sNext*nextPi)*(a*sOld)≤b*sNext*(sOld*oldPi) := by exact_mod_cast h0
  have h0N : a*sOld*(sNext*nextPi)≤b*sNext*(sOld*oldPi) := by simpa only [Nat.mul_comm] using h0N'
  refine ⟨(scaled_step_iff a b oldPi nextPi sOld sNext hOld hNext).mp h0N, ?_, ?_⟩
  · have hh : nextB*p≤9*oldB := by exact_mod_cast h1
    simpa only [Nat.mul_comm] using hh
  · have hh : nextC*p≤9*oldC := by exact_mod_cast h2
    simpa only [Nat.mul_comm] using hh
end ThreeSum.WeightedGlobalPairedSelectedChain
