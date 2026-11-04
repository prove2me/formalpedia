-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCountReady.ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:57:26.739213+00:00
-- url     : https://prove2.me/submissions/95ac8aeb-5d15-4ba6-9a2d-518823523037

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_bank_size
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_bank_pos
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_rows_le
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
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
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_sorted
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_cost
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_program_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sourceArgs_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_source_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sources_length
import Theorems.Thm_ThreeSum_LightTernaryWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedRows_program_length
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_dimensions
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
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
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_zero
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
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_bank_pos
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearCanonical_read_of_seg
import Theorems.Thm_ThreeSum_TernaryNearCanonical_sorted
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_length
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_read_three
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankCanonical_read_of_seg
import Theorems.Thm_ThreeSum_WeightedBankCanonical_sorted
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedFrontendResources_bank_controls
import Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_ThreeSum_WeightedFrontendResources_plan
import Theorems.Thm_ThreeSum_WeightedFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontendResources_plan
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_address
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_group_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_same_type
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_typed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_left_input
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_right_input
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_homogeneous
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_prepared_time_sourceConfig
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_bank_pos
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_cost_eq_counts
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_bank_controls
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_controls
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_plan
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_raws_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_wordCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_output
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_right
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearCanonical_read_of_seg
import Theorems.Thm_ThreeSum_WeightedNearCanonical_sorted
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
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightTernaryCountFrontend.program_length
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightTernaryGroupedBanks.program_length
attribute [local simp] ThreeSum.LightTernaryMomentChannelStep.callArgs_cost
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
attribute [local simp] ThreeSum.LightTernaryNearSetup.program_length
attribute [local simp] ThreeSum.LightTernaryPreparedWanted.program_length
attribute [local simp] ThreeSum.LightTernaryRequesterMatrix.program_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.args_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.callArgs_cost
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.program_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.sourceArgs_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.source_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.sources_length
attribute [local simp] ThreeSum.LightTernaryWantedQuery.program_length
attribute [local simp] ThreeSum.LightTernaryWantedRows.program_length
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
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryBankStageModel.forwardStage_zero
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
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.TernaryWantedBatchIndex.cells_length
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
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
attribute [local simp] ThreeSum.WeightedFrontendResources.sourceConfig_config
attribute [local simp] ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input
attribute [local simp] ThreeSum.WeightedGlobalArenaSourceSetup.setup_right_input
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig
attribute [local simp] ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mapCodes_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.raws_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.wordCodes_length
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_output
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
attribute [local simp] ThreeSum.WeightedGlobalNativePairAccess.mem_pair
attribute [local simp] ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits


noncomputable section
namespace ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
private theorem four_pow (n : ℕ) : 4^n=2^(2*n) := by rw [Nat.pow_mul]
private theorem grouped_end {base group groups N nb : ℕ} (hg : group<groups) :
    base+group*((N+1)*nb)+N*nb+nb≤base+groups*((N+1)*nb) := by
  have hh := Nat.mul_le_mul_right ((N+1)*nb) (Nat.succ_le_of_lt hg)
  nlinarith
end ThreeSum.WeightedGlobalArenaCountReady
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaCountReady
theorem _root_.solution {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : Capacity (lim := lim) (d := d) (r := r) maps τ cap I)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hrecords : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I)))
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    WeightedCountExecutionFactory.Ready (front (r := r) maps τ cap localQ I) lim d μ
      ((source (r := r) maps cap I false).values (WeightedBankCanonical.enumeration (N m r) (cut m r)).word leftWeight)
      ((source (r := r) maps cap I true).values (WeightedBankCanonical.enumeration (N m r) (cut m r)).word rightWeight) := by
  let n := N m r
  let A := valueCap (r := r) maps cap I
  let S := front (r := r) maps τ cap localQ I
  have hn : nb m r<2^(2*n) := bank_size hN
  have hnC : n≤I.capacity := by
    have := C.powers
    dsimp [n]
    omega
  have hcountC : S.count≤I.capacity := by
    have := C.records
    dsimp [S,front]
    omega
  have h54 : addr I.free I.capacity 54≤lim.space := (before (i := 54) (j := slots) (by decide) (by omega : 0≤I.capacity)).trans C.endSpace
  have hstageF : S.fbase+S.groups*((n+1)*nb m r)≤S.gbase := before (by decide) C.stages
  have hstageG : S.gbase+S.groups*((n+1)*nb m r)≤S.hbase := before (by decide) C.stages
  have hstageH : S.hbase+S.groups*((n+1)*nb m r)≤S.dst := before (by decide) C.stages
  have hDst : S.dst+S.count≤addr I.free I.capacity 54 := before (by decide) hcountC
  obtain ⟨wlookup,wN,wstride,wtail,wforward,wproduct,winverse⟩ :=
    WeightedGlobalFrontendResources.bank_controls n (nb m r) (F^r) S.count (3^n) A
  obtain ⟨_,_,_,_,_,_,_,wgroup,wcount⟩ :=
    WeightedGlobalFrontendResources.controls n (nb m r) (F^r) S.count (3^n) A
  have w := C.word
  refine {
    hw:=hw
    ha:=C.prefixBank
    hfs:=before (by decide) C.bankValues
    hgs:=before (by decide) C.bankValues
    hmeta:=before (by decide) C.metadata
    hpows:=before (by decide) C.powers
    hfg:=hstageF
    hgh:=hstageG
    hHdst:=hstageH
    hword:=(Int.ofNat_le.mpr wlookup).trans w
    hNword:=?_
    hgroupsWord:=?_
    hcodes:=WeightedBankCanonical.read_of_seg μ hcodes
    hsorted:=WeightedBankCanonical.sorted n (cut m r)
    hF:=fun g hg W => WeightedGlobalArenaSourceValues.bound maps cap I false leftWeight g W hleft
    hG:=fun g hg W => WeightedGlobalArenaSourceValues.bound maps cap I true rightWeight g W hright
    hforwardWord:=?_
    hproductWord:=(Int.ofNat_le.mpr wproduct).trans w
    hinverseWord:=?_
    hL:=le_rfl
    hn:=hn
    hrecords:=before (by decide) C.records
    hdst:=hDst
    hspace:=h54
    hreadGroup:=?_
    hreadQ:=?_
    hgroup:=?_
    hRank:=?_
    hcountWord:=?_
    hstrideWord:=(Int.ofNat_le.mpr wstride).trans w
    htailWord:=(Int.ofNat_le.mpr wtail).trans w
    hplan:=?_
    htime:=?_
    hd:=by
      have := C.depth
      dsimp [front,nearConfig,WeightedGlobalArenaFrontendResources.config]
      omega }
  · exact_mod_cast (Int.ofNat_le.mpr wN).trans w
  · exact_mod_cast (Int.ofNat_le.mpr wgroup).trans w
  · exact_mod_cast (Int.ofNat_le.mpr wforward).trans w
  · exact_mod_cast (Int.ofNat_le.mpr winverse).trans w
  · intro j hj
    exact (TernaryWantedBatchIndex.read_three _ hrecords hj).2.2
  · intro j hj
    have hh := (TernaryWantedBatchIndex.read_three _ hrecords hj).2.1
    rw [←WeightedGlobalArenaQueryModel.setup_address (τ := τ) (cap := cap) (localQ := localQ) hj] at hh
    exact hh
  · intro j hj
    exact WeightedGlobalArenaQueryModel.setup_group_lt hF hj
  · intro j hj
    change cacheCost ((setup (r := r) maps τ cap localQ I).front.Q j)=cacheCost ((setup (r := r) maps τ cap localQ I).front.Qstar)
    rw [WeightedGlobalDimensionBounds.cost_eq_counts,WeightedGlobalDimensionBounds.cost_eq_counts]
    rw [WeightedGlobalArenaQueryModel.setup_same_type hj 1,WeightedGlobalArenaQueryModel.setup_same_type hj 2]
  · exact_mod_cast (Int.ofNat_le.mpr wcount).trans w
  · intro j hj
    have hg := WeightedGlobalArenaQueryModel.setup_group_lt (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) hF hj
    change S.group j<F^r at hg
    have hFend := (grouped_end (base := S.fbase) (N := n) (nb := nb m r) hg).trans hstageF
    have hGend := (grouped_end (base := S.gbase) (N := n) (nb := nb m r) hg).trans hstageG
    have hHend := (grouped_end (base := S.hbase) (N := n) (nb := nb m r) hg).trans hstageH
    have ha : alphaRank m=3258243765000*m := by
      unfold alphaRank fixedAlpha
      change 2672750671000*m+2*(292746547000*m)=3258243765000*m
      ring
    have hs : 1025*(r*alphaRank m)≤2*cut m r := by
      rw [ha]
      dsimp [cut,LightWeightedGlobalPrefixSetup.T]
      nlinarith
    have ht : cut m r≤1025*n := by
      simpa [cut,n,N,LightWeightedGlobalPrefixSetup.N,fixedLength,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using (LightWeightedGlobalPrefixSetup.dimensions m r).2.2
    have hDegree : r*alphaRank m≤2*n := by
      rw [ha]
      dsimp [n,N,LightWeightedGlobalPrefixSetup.N,fixedLength]
      nlinarith
    have hout : cut m r<cacheCost (S.Q j) := by
      change cut m r<cacheCost ((setup (r := r) maps τ cap localQ I).front.Q j)
      rw [WeightedGlobalDimensionBounds.cost_eq_counts,
        WeightedGlobalArenaQueryModel.setup_typed (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) hj 1,
        WeightedGlobalArenaQueryModel.setup_typed (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) hj 2]
      have hpos : 0<r*m := by
        dsimp [N,fixedLength] at hN
        nlinarith
      dsimp [cut,LightWeightedGlobalPrefixSetup.T,fixedPi]
      nlinarith
    have hH54 : S.hbase+S.group j*((n+1)*nb m r)+(n+1)*nb m r≤addr I.free I.capacity 54 := by
      simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using
        (hHend.trans (before (i := 53) (j := 54) (by decide) (by omega : 0≤I.capacity)))
    have hp := WeightedGlobalArenaFrontendResources.plan (S.Q j) S.E
      ((source (r := r) maps cap I false).values S.E.word leftWeight (S.group j))
      ((source (r := r) maps cap I true).values S.E.word rightWeight (S.group j))
      (rows_le (S.Q j)) C.nearRows hnC C.powers C.nearMetadata C.division ht hDegree hDegree hs hs hn
      ((rows_le (S.Q j)).trans_lt (by exact (Nat.pow_lt_pow_left (by decide) (by omega) : 3^n<4^n) |>.trans_eq (four_pow n)))
      bank_pos (C.prefixBank.trans (before (by decide) (by omega : 0≤I.capacity)))
      (hFend.trans (before (by decide) (by omega : 0≤I.capacity)))
      (hGend.trans (before (by decide) (by omega : 0≤I.capacity)))
      hH54
      C.endSpace hw C.word
      (WeightedGlobalArenaSourceValues.homogeneous maps cap I false leftWeight (S.group j))
      (WeightedGlobalArenaSourceValues.homogeneous maps cap I true rightWeight (S.group j))
      (fun W => WeightedGlobalArenaSourceValues.bound maps cap I false leftWeight (S.group j) W hleft)
      (fun W => WeightedGlobalArenaSourceValues.bound maps cap I true rightWeight (S.group j) W hright)
      hout (WeightedBankCanonical.sorted n (cut m r))
    exact hp
  · intro j hj
    rw [WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig]
    apply le_trans _ C.time
    exact Finset.le_sup (f := fun Q => LightWeightedPreparedWanted.time
      (nearConfig (m := m) (r := r) I false A) (nearConfig (m := m) (r := r) I true A) Q)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,WeightedGlobalArenaQueryModel.setup_typed hj⟩)
end ThreeSum.WeightedGlobalArenaCountReady
