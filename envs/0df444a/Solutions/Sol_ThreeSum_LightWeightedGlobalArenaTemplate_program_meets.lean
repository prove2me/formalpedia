-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalArenaTemplate.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:14:18.763558+00:00
-- url     : https://prove2.me/submissions/b502ef56-915c-4cd6-8d4e-99409723be25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_hostFields_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_seedFields_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_fields_good
import Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_stores_ends
import Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_value_congr
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockIndex_coordEquiv_val
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_card
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
import Theorems.Thm_ThreeSum_BlockIndex_unindex_index
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_pos
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_source_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sources_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_capacity_pos
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
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
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockIndex.coordEquiv_val
attribute [local simp] ThreeSum.BlockIndex.indexSet_card
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_union
attribute [local simp] ThreeSum.BlockIndex.index_unindex
attribute [local simp] ThreeSum.BlockIndex.mem_indexSet
attribute [local simp] ThreeSum.BlockIndex.unindex_index
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.args_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.callArgs_cost
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.source_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.sources_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
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
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
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
attribute [local simp] ThreeSum.LightWeightedGlobalArenaTemplate.hostFields_length
attribute [local simp] ThreeSum.LightWeightedGlobalArenaTemplate.seedFields_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalArenaTemplate
theorem _root_.solution {lim : Limits} {D E U free q d : ℕ} (inputs : List ℤ) (hlen : inputs.length = 23) (μ : ℕ → ℤ)
    (hU : inputs.getD 0 0 = (U : ℤ)) (hFree : inputs.getD 1 0 = (free : ℤ)) (hq : inputs.getD 16 0 = (q : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (hend : finish free (capacity D E U) ≤ lim.space) (hUW : (U : ℤ) + 1 ≤ lim.word)
    (hEW : (E : ℤ) ≤ lim.word) (hqC : q * q ≤ capacity D E U) (hd : d < lim.depth) :
    Meets lim (program D E) 1 d inputs μ (time E)
      (fun r ν =>
        r = (free : ℤ) ∧
          Seg ν (addr free (capacity D E U) 0) (hostValues (frame inputs) free (capacity D E U)) ∧
            Seg ν (addr free (capacity D E U) 2) (seedValues (frame inputs) free (capacity D E U)) ∧ Kept μ ν free) :=
  by
  change inputs[0]?.getD 0 = (U : ℤ) at hU
  change inputs[1]?.getD 0 = (free : ℤ) at hFree
  change inputs[16]?.getD 0 = (q : ℤ) at hq
  let C := capacity D E U
  have hCmin : 256 ≤ C := capacity_pos D E U
  have hCspace : C ≤ lim.space := by unfold finish addr slots at hend; change free + 67 * C ≤ lim.space at hend; omega
  have hCword : (C : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hCspace).trans hw
  have hpowpos : 1 ≤ (U + 1) ^ E := Nat.one_le_pow _ _ (by omega)
  have hcoeff : 256 * (D + 1) ≤ C := by dsimp [C, capacity]; nlinarith
  have hcoeffWord : ((256 * (D + 1) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcoeff).trans hCword
  have hpow : ∀ i ≤ E, (((U + 1) ^ i : ℕ) : ℤ) ≤ lim.word :=
    by
    intro i hi
    have hh := Nat.pow_le_pow_right (by omega : 1 ≤ U + 1) hi
    have hm : (U + 1) ^ E ≤ C := by dsimp [C, capacity]; nlinarith
    exact (Int.ofNat_le.mpr (hh.trans hm)).trans hCword
  have hp := (LightNatPower.program_meets (d := d + 1) μ hEW hpow).append [body D E]
  apply Meets.of_body (by rfl)
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, frame, hU]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [frame, hU] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, frame, hU] <;> omega)
    on_goal -1 => (rintro pow μp ⟨hpowResult, hμp⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μp
  have hcapProduct : (256 * (D + 1) : ℤ) * (((U + 1) ^ E : ℕ) : ℤ) = (C : ℤ) := by dsimp [C, capacity]
  have hcapNonneg : 0 ≤ (256 * (D + 1) : ℤ) * (((U + 1) ^ E : ℕ) : ℤ) := by positivity
  have hPowLocal : (setLocal inputs 23 pow)[23]?.getD 0 = (((U + 1) ^ E : ℕ) : ℤ) :=
    by
    change frame (setLocal inputs 23 pow) 23 = _
    rw [frame_setLocal]
    simpa using hpowResult
  have hmulNonneg : 0 ≤ (256 * (D + 1) : ℤ) * (setLocal inputs 23 pow)[23]?.getD 0 :=
    by
    rw [hPowLocal]
    positivity
  have hmulWord : (256 * (D + 1) : ℤ) * (setLocal inputs 23 pow)[23]?.getD 0 ≤ lim.word :=
    by
    rw [hPowLocal, hcapProduct]
    exact hCword
  have hmulNonnegFull : 0 ≤ 256 * ((D : ℤ) + 1) * ((U : ℤ) + 1) ^ E := by positivity
  have hmulWordFull : 256 * ((D : ℤ) + 1) * ((U : ℤ) + 1) ^ E ≤ lim.word :=
    by
    dsimp [C, capacity] at hCword
    exact_mod_cast hCword
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen C ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPowLocal, hcapProduct, capacity, C]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPowLocal, hcapProduct, capacity, C] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPowLocal, hcapProduct, capacity, C] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  let loc := frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ))
  have hlocFree : loc 1 = (free : ℤ) :=
    by
    change frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ)) 1 = _
    rw [frame_setLocal, if_neg (by decide), frame_setLocal, if_neg (by decide)]
    exact hFree
  have hlocC : loc 24 = (C : ℤ) :=
    by
    change frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ)) 24 = _
    rw [frame_setLocal, if_pos rfl]
  have hlocInitial : ∀ i < 23, loc i = frame inputs i :=
    by
    intro i hi
    simp only [loc, frame_setLocal]
    rw [if_neg (by omega), if_neg (by omega)]
  have hlocQ : loc 16 = (q : ℤ) := by rw [hlocInitial 16 (by decide)]; exact hq
  have hSquare : |loc 16 * loc 16| ≤ lim.word :=
    by
    rw [hlocQ, abs_of_nonneg (by positivity)]
    exact_mod_cast (Int.ofNat_le.mpr hqC).trans hCword
  have hgoodHost : ∀ f ∈ hostFields, Good f := fun f hf => fields_good f (List.mem_append_left _ hf)
  have hgoodSeed : ∀ f ∈ seedFields, Good f := fun f hf => fields_good f (List.mem_append_right _ hf)
  have hhostSpace : addr free C 0 + 0 + hostFields.length ≤ lim.space := by
    simpa only [Nat.add_zero] using
      region_space (slot := 0) (by decide : 0 < slots) (show hostFields.length ≤ C by rw [hostFields_length]; omega)
        hend
  have hseedSpace : addr free C 2 + 0 + seedFields.length ≤ lim.space := by
    simpa only [Nat.add_zero] using
      region_space (slot := 2) (by decide : 2 < slots) (show seedFields.length ≤ C by rw [seedFields_length]; omega)
        hend
  have hs0 :=
    stores_ends (P := program D E) (depth := d) hostFields 0 loc μ hlocFree hlocC (by omega) hw hend (by decide)
      hhostSpace hgoodHost hSquare
  change Ends _ _ _ _ ⟨loc, μ⟩ _ _
  refine
    Ends.pieceThen hs0 ?_ (hT := by
      simp only [hostFields_length]
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  rintro ⟨loc₀, μ₀⟩ ⟨hloc₀, hhost, hkeep₀⟩
  dsimp only at hloc₀
  subst loc₀
  change Seg μ₀ (addr free C 0 + 0) _ at hhost
  change SameOutside μ μ₀ (addr free C 0 + 0) hostFields.length at hkeep₀
  simp only [Nat.add_zero] at hhost hkeep₀
  have hs1 :=
    stores_ends (P := program D E) (depth := d) seedFields 0 loc μ₀ hlocFree hlocC (by omega) hw hend (by decide)
      hseedSpace hgoodSeed hSquare
  refine
    Ends.pieceThen hs1 ?_ (hT := by
      simp only [hostFields_length, seedFields_length]
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  rintro ⟨loc₁, ν⟩ ⟨hloc₁, hseed, hkeep₁⟩
  dsimp only at hloc₁
  subst loc₁
  change Seg ν (addr free C 2 + 0) _ at hseed
  change SameOutside μ₀ ν (addr free C 2 + 0) seedFields.length at hkeep₁
  simp only [Nat.add_zero] at hseed hkeep₁
  refine
    Ends.setLast ?_ (hs := trivial) (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hostFields_length, seedFields_length,
            Expr.cost]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hostFields_length, seedFields_length, Expr.cost] <;> first
            | omega
            | (ring_nf; omega)))
  refine ⟨hlocFree, ?_, ?_, ?_⟩
  · have hmaps : hostFields.map (value loc free C) = hostValues (frame inputs) free C :=
      by
      apply List.map_congr_left
      intro f hf
      exact value_congr hlocInitial f (hgoodHost f hf)
    rw [← hmaps]
    intro i hi
    change ν (addr free C 0 + i) = _
    rw [hkeep₁ _
        (Or.inl
          (by
            have hb := before (free := free) (C := C) (i := 0) (j := 2) (len := 106) (by decide) (by omega)
            simp only [List.length_map, hostFields_length] at hi
            omega))]
    simpa only [Nat.add_zero] using hhost i hi
  · have hmaps : seedFields.map (value loc free C) = seedValues (frame inputs) free C :=
      by
      apply List.map_congr_left
      intro f hf
      exact value_congr hlocInitial f (hgoodSeed f hf)
    rw [← hmaps]
    simpa only [Nat.add_zero] using hseed
  · intro x hx
    change ν x = μ x
    rw [hkeep₁ x (Or.inl (by unfold addr; omega)), hkeep₀ x (Or.inl (by unfold addr; omega))]
end ThreeSum.LightWeightedGlobalArenaTemplate
