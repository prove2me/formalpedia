-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixPrepare.ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:33:53.914618+00:00
-- url     : https://prove2.me/submissions/e466d19d-defb-448c-8cc9-62a4caacb50c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
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
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_program_length
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightStoredSpan_program_length
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
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_digit
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_divide
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_polynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_powers
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_row
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
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixFinish_header_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patchList_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_resultHeader_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_prefix_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_tail_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedController_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_spanAppend_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_wanted_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withCollision_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withDivision_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_withWanted_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_channelLibraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_potentialLibraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_program_main
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_quadLibraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorHeader_args_cost
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_flag_menu_iff
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_length
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
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_left_input
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_right_input
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_raws_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_wordCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_output
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_right
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_result_length
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
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
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightOriginalCollisionScore.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightStoredSpan.program_length
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
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_digit
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_divide
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_polynomial
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_powers
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_row
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
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixFinish.header_length
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixHeader.patchList_length
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixHeader.resultHeader_length
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixLoop.prefix_length
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixLoop.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalPrefixLoop.tail_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedController.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.wanted_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.withCollision_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.withDivision_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.withWanted_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.channelLibraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.potentialLibraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.program_main
attribute [local simp] ThreeSum.LightWeightedGlobalTensorDriver.quadLibraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalTensorHeader.args_cost
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
attribute [local simp] ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff
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
attribute [local simp] ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mapCodes_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.raws_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.wordCodes_length
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_output
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
attribute [local simp] ThreeSum.WeightedGlobalNativePairAccess.mem_pair
attribute [local simp] ThreeSum.WeightedGlobalPrefixSeedHeader.result_length
attribute [local simp] ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaPrefixPrepare
theorem _root_.solution {lim : Limits} {p m F j J n U0 a b scale depth : ℕ}
    (I : Input) (Q : WeightedGlobalGoodOutputCatalog.Output m) (μ : ℕ→ℤ)
    (hm : 0<m) (hw : (lim.space:ℤ)≤lim.word)
    (hcap : envelope (inputs p m F j J n U0 a b scale I Q)≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space)
    (hdepth : depth+LightWeightedGlobalPrefixSetup.N m (j+1)+5≤lim.depth)
    (hF : μ (addr I.free I.capacity 0+99)=(addr I.free I.capacity 50:ℤ))
    (hG : μ (addr I.free I.capacity 0+100)=(addr I.free I.capacity 51:ℤ))
    (hbudget : Seg μ (addr I.free I.capacity 3+41)
      (LightTernaryBudgetStep.oldValues (p^j) (p^j) (a^j) (9^j*(n*n)) (9^j*(n*n)) (U0*(b*scale)^j))) :
    PrepareReady (inputs p m F j J n U0 a b scale I Q) lim depth μ :=by
  let X:=inputs p m F j J n U0 a b scale I Q
  have h106 : 106≤I.capacity:=by unfold envelope at hcap;omega
  have hfp : footprint X≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;omega
  have hpw : LightWeightedGlobalPrefixSetup.word m (j+1) F≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;exact Nat.le_trans (by dsimp [X,inputs];omega) hcap
  have hsum : (scalars X).sum≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;omega
  have hcspace : I.capacity≤lim.space:=by unfold finish addr slots at hspace;omega
  have hnum (z : ℕ) (hz : z∈scalars X) : z≤I.capacity:=
    (List.single_le_sum (fun x _=>Nat.zero_le x) z hz).trans hsum
  have hnumW (z : ℕ) (hz : z∈scalars X) : (z:ℤ)≤lim.word:=
    (Int.ofNat_le.mpr ((hnum z hz).trans hcspace)).trans hw
  have hscalarLength : (scalars X).length=31:=rfl
  have hnumIndex (i : ℕ) (hi : i<31) : (scalars X)[i]'(by omega)≤I.capacity:=
    hnum _ (List.getElem_mem (by omega))
  have hwordIndex (i : ℕ) (hi : i<31) : (((scalars X)[i]'(by omega)):ℤ)≤lim.word:=
    (Int.ofNat_le.mpr ((hnumIndex i hi).trans hcspace)).trans hw
  have hfitIndex (i : ℕ) (hi : i<31) : |(((scalars X)[i]'(by omega)):ℤ)|≤lim.word:=by
    simpa only [Int.natCast_nonneg,abs_of_nonneg] using hwordIndex i hi
  have hPointer (z : ℕ) (hz : z≤lim.space) : |(z:ℤ)|≤lim.word:=by
    simpa only [Int.natCast_nonneg,abs_of_nonneg] using (Int.ofNat_le.mpr hz).trans hw
  have hEnd : LightWeightedGlobalPrefixSetup.endAt X.prefixFree X.m (X.j+1)≤lim.space :=by
    change addr I.free I.capacity 13+4^(LightWeightedGlobalPrefixSetup.N m (j+1))+(2*LightWeightedGlobalPrefixSetup.N m (j+1)+1)+8≤lim.space
    have hh:=region_space (free:=I.free) (slot:=13) (by decide : 13<slots) hfp hspace
    dsimp only [footprint,X,inputs] at hh
    omega
  have hTail : LightWeightedGlobalPrefixSetup.N X.m (X.j+1)*LightWeightedGlobalPrefixSetup.nb X.m (X.j+1)≤I.capacity:=
    hnumIndex 19 (by decide)
  have hFtail : X.Fbase+LightWeightedGlobalPrefixSetup.N X.m (X.j+1)*LightWeightedGlobalPrefixSetup.nb X.m (X.j+1)≤lim.space:=
    region_space (by decide : 50<slots) hTail hspace
  have hGtail : X.Gbase+LightWeightedGlobalPrefixSetup.N X.m (X.j+1)*LightWeightedGlobalPrefixSetup.nb X.m (X.j+1)≤lim.space:=
    region_space (by decide : 51<slots) hTail hspace
  have hbank : X.prefixFree≤lim.space:=by dsimp [LightWeightedGlobalPrefixSetup.endAt,LightWeightedGlobalPrefixSetup.headerAt,LightWeightedGlobalPrefixSetup.workAt] at hEnd;generalize 4^(LightWeightedGlobalPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have hwork : LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1)≤lim.space:=by dsimp [LightWeightedGlobalPrefixSetup.endAt,LightWeightedGlobalPrefixSetup.headerAt] at hEnd;generalize 4^(LightWeightedGlobalPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have hhdr : LightWeightedGlobalPrefixSetup.headerAt X.prefixFree X.m (X.j+1)≤lim.space:=by dsimp [LightWeightedGlobalPrefixSetup.endAt] at hEnd;generalize 4^(LightWeightedGlobalPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have htemplate : X.template≤lim.space:=by exact (before (free:=I.free) (C:=I.capacity) (by decide : 0<13) (show 0≤I.capacity by omega)).trans hbank
  have hhost : X.liveHeader≤lim.space:=by exact (before (free:=I.free) (C:=I.capacity) (by decide : 1<13) (show 0≤I.capacity by omega)).trans hbank
  refine {
    spaceWord:=hw
    prefixSpace:=hEnd
    prefixWord:=(Int.ofNat_le.mpr (hpw.trans hcspace)).trans hw
    depthBound:=hdepth
    jWord:=hwordIndex 0 (by decide)
    templateEnd:=before (by decide : 0<1) h106
    headerEnd:=before (by decide : 1<3) h106
    seedEnd:=before (by decide : 3<13) (by omega)
    Fread:=hF
    Gread:=hG
    cutoff:=?_
    Nword:=?_
    scalarWords:=?_
    factorWords:=?_
    queryWords:=?_
    budgetRead:=hbudget
    budgetWords:=?_
    midWord:=hwordIndex 29 (by decide)
    nineWord:=hwordIndex 30 (by decide) }
  · change LightWeightedGlobalPrefixSetup.T m (j+1)+1024≤(1024*(alphaRank m*(j+1))+3*(fixedAlpha m 2*(j+1)))
    dsimp [LightWeightedGlobalPrefixSetup.T,alphaRank,fixedAlpha]
    have hpos : 1≤(j+1)*m:=by nlinarith
    nlinarith
  · change (LightWeightedGlobalPrefixSetup.N X.m (X.j+1):ℤ)+1≤lim.word
    have hh:=hwordIndex 11 (by decide)
    change ((2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1):ℕ):ℤ)≤lim.word at hh
    have hN : 1≤LightWeightedGlobalPrefixSetup.N X.m (X.j+1):=by dsimp [X,inputs,LightWeightedGlobalPrefixSetup.N];nlinarith
    omega
  · intro x hx
    simp only [LightWeightedGlobalPrefixHeader.args,LightWeightedGlobalPrefixHeader.locals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h|h
    · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hPointer _ htemplate
      · exact hPointer _ hhost
      · exact hPointer _ hhdr
      · exact hfitIndex 0 (by decide)
      · exact hfitIndex 1 (by decide)
      · exact hfitIndex 2 (by decide)
      · exact hfitIndex 3 (by decide)
      · exact hfitIndex 4 (by decide)
      · exact hfitIndex 5 (by decide)
      · exact hfitIndex 6 (by decide)
      · exact hfitIndex 7 (by decide)
      · exact hfitIndex 8 (by decide)
    · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hfitIndex 9 (by decide)
      · exact hfitIndex 10 (by decide)
      · exact hfitIndex 11 (by decide)
      · exact hfitIndex 12 (by decide)
      · exact hfitIndex 13 (by decide)
      · exact hPointer _ hbank
      · exact hPointer _ hwork
      · exact hfitIndex 14 (by decide)
      · exact hfitIndex 15 (by decide)
      · exact hfitIndex 16 (by decide)
      · exact hfitIndex 17 (by decide)
      · exact hfitIndex 18 (by decide)
      · exact hfitIndex 19 (by decide)
      · exact hfitIndex 20 (by decide)
      · exact hfitIndex 21 (by decide)
      · exact hfitIndex 22 (by decide)
      · exact hPointer _ hFtail
      · exact hPointer _ hGtail
  · intro i hi
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0<2) hi)).trans
      (hwordIndex 16 (by decide))
  · intro i hi
    have hradix : 1≤X.radix:=by dsimp [X,inputs];exact Nat.one_le_pow _ _ (by decide)
    have hm : Monotone (LightTernaryRepeatWord.value X.localQ X.radix):=monotone_nat_of_le_succ (fun i=>by
      simp only [LightTernaryRepeatWord.value]
      nlinarith)
    have hh:=hm hi
    exact (Int.ofNat_le.mpr hh).trans (hwordIndex 22 (by decide))
  · intro x hx
    simp only [LightTernaryBudgetStep.nextValues,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hwordIndex 23 (by decide)
    · exact hwordIndex 24 (by decide)
    · exact hwordIndex 25 (by decide)
    · exact hwordIndex 26 (by decide)
    · exact hwordIndex 27 (by decide)
    · exact hwordIndex 28 (by decide)
end ThreeSum.WeightedGlobalArenaPrefixPrepare
