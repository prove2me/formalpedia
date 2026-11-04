-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.all_host_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:22:09.142539+00:00
-- url     : https://prove2.me/submissions/494d2351-dc8c-498e-93f9-653dc2bde2d0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_hostConstant_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_all_host_prefix_bound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
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
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
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
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_cost
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_flag_zero
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
import Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentDriver_library_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_driver_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_length
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
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_append
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_cons
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_nil
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_flag_menu_iff
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
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
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_left_input
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_right_input
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_prepared_time_sourceConfig
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_raws_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_wordCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_output
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_right
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_padded_carry_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_polynomial_digit_budget
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
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
attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target
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
attribute [local simp] ThreeSum.LightTernaryFixedChannelLoop.arguments_cost
attribute [local simp] ThreeSum.LightTernaryFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightTernaryGroupedBanks.program_length
attribute [local simp] ThreeSum.LightTernaryMomentBatch.flag_zero
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
attribute [local simp] ThreeSum.LightWeightedGlobalCertifiedMomentDriver.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalMomentDriver.library_length
attribute [local simp] ThreeSum.LightWeightedGlobalMomentReporter.driver_length
attribute [local simp] ThreeSum.LightWeightedGlobalMomentReporter.program_length
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
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_append
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_cons
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_nil
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



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualPrefixRuntime
theorem _root_.solution {K k b m κ F D E β : ℕ} {δ ε : ℝ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→ℕ→Input) (U : ℕ→ℕ)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hβ : 1<β)
    (hU : ∀n, 1<n → U n≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b)
    (hB : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nB≤n)
    (hC : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nC≤n)
    (hrequest : ∀n, 1<n → ∀j≤radixLength m n,
      (I n j).requesterCount≤n*2^WeightedGlobalSignedPadding.paddedLength β (U n) (radixLength m n))
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀n, 1<n → ∀j≤radixLength m n,
      WeightedGlobalFrontendResources.eulerBound (N m j)
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) (I n j))≤D*(n+U n+1)^E)
    (htime : ∀n, 1<n → ∀j≤radixLength m n, (I n j).queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ) (hε : 0<ε)
    (hgap : fullExponent K k c d m+δ+ε<WeightedGlobalParameters.targetExponent) :
    ∀ᶠ n : ℕ in atTop,
      (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤(n:ℝ)^WeightedGlobalParameters.targetExponent :=by
  let A:=hostConstant K k c d m F D E κ
  have hA : 0≤A:=hostConstant_nonneg _ _ _ _ _ _ _ _ _
  have hκ : (0:ℝ)≤κ:=Nat.cast_nonneg _
  have hUR : ∀n, 1<n → (U n:ℝ)≤(n:ℝ)^(κ:ℝ):=by
    intro n hn
    simpa only [Real.rpow_natCast,Nat.cast_pow] using (show (U n:ℝ)≤(n^κ:ℕ) by exact_mod_cast hU n hn)
  have hc:=WeightedGlobalSignedPadding.padded_carry_eventually hgood.1 hβ hκ hcarry U hUR
  have hp:=WeightedGlobalSignedPreparationBudget.polynomial_digit_budget hgood.1 hβ hκ hε A hA 4 U hUR
  filter_upwards [hc,hp,eventually_gt_atTop (1:ℕ)] with n hcarryN hpolyN hn
  let J:=WeightedGlobalSignedPadding.paddedLength β (U n) (radixLength m n)
  have hJ : radixLength m n+1≤J+1:=by
    dsimp [J,WeightedGlobalSignedPadding.paddedLength]
    omega
  have hbinary : 1≤((Nat.log 2 (3*U n+1):ℝ)+2)^4:=one_le_pow₀ (by
    have hh : (0:ℝ)≤Nat.log 2 (3*U n+1):=Nat.cast_nonneg _
    linarith)
  have hdrop : A*(J+1:ℕ)^4≤(n:ℝ)^ε:=by
    have hh:=le_mul_of_one_le_right (show (0:ℝ)≤A*(J+1:ℕ)^4 from mul_nonneg hA (by positivity)) hbinary
    exact hh.trans (by simpa [J] using hpolyN)
  have htimeN:=all_host_prefix_bound (n:=n) (U:=U n) (κ:=κ)
    (carries:=2^J) (D:=D) (E:=E) maps Q (I n) hK hk hgood hn (hU n hn) hFpos hF hb
    (Nat.one_le_pow _ _ (by decide)) (hB n hn) (hC n hn) (hrequest n hn)
    hposL hposR (hword n hn) (htime n hn) c d hpoly
  have hRpow : ((radixLength m n+1:ℕ):ℝ)^4≤((J+1:ℕ):ℝ)^4:=by exact_mod_cast Nat.pow_le_pow_left hJ 4
  have hfinite : (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤
      A*(J+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=by
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow hA)
        (show (0:ℝ)≤(2:ℝ)^J by positivity)) (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
    have hh0 : (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤
        A*(radixLength m n+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=by
      simpa only [A,Nat.cast_pow,Nat.cast_ofNat] using htimeN
    exact hh0.trans hh
  have hCarry : (2:ℝ)^J≤(n:ℝ)^δ:=by simpa only [J] using hcarryN
  have hsmall:=mul_le_mul hdrop hCarry (by positivity) (show (0:ℝ)≤(n:ℝ)^ε by positivity)
  have hsmall':=mul_le_mul_of_nonneg_right hsmall (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  have hnR : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hn
  calc
    _≤A*(J+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=hfinite
    _≤(n:ℝ)^ε*(n:ℝ)^δ*(n:ℝ)^fullExponent K k c d m:=hsmall'
    _=(n:ℝ)^(fullExponent K k c d m+δ+ε):=by rw [←Real.rpow_add hnR,←Real.rpow_add hnR]; congr 1; ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hgap.le
end ThreeSum.WeightedGlobalActualPrefixRuntime
