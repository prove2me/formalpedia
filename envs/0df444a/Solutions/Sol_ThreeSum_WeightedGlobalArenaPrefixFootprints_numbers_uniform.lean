-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.numbers_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:38:16.600663+00:00
-- url     : https://prove2.me/submissions/ec38789c-037d-4e31-b8a7-a96b92427405

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_inputN
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_inputU
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_prefixCount
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_digits
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_alphabet
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_carries
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Numbers_sum_list
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
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
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
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_raws_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_wordCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
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
attribute [local simp] ThreeSum.WeightedGlobalNativePairAccess.mem_pair
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

open Lean Elab Tactic Meta
namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
theorem _root_.solution {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    Uniform M (total maps τ cap M b K H drift scale) := by
  have hn := inputN M
  have hU := inputU M
  have hj := prefixCount hM
  have hJ := digits hM hb
  have hcarry := carries hM hb
  have hpow (A : ℕ) := alphabet hM A
  have hN : Uniform M (fun _ _ j=>fixedLength m*j) := (Uniform.const M _).mul hj
  have hW : Uniform M (fun _ _ j=>(sourceWidth maps cap)^j) := hpow _
  have hZ : Uniform M (fun _ _ j=>(wantedWidth maps τ)^j) := hpow _
  have hQ : Uniform M (fun _ _ j=>(4^fixedLength m)^j) := hpow _
  have hP : Uniform M (fun _ _ j=>(p+1)^j) := hpow _
  have hFp : Uniform M (fun _ _ j=>F^j) := hpow _
  have hF : Uniform M (fun _ _ j=>(F+1)^j) := hpow _
  have hR : Uniform M (fun _ _ j=>(4^fixedLength m+1)^j) := hpow _
  have hp : Uniform M (fun _ _ j=>p^j) := hpow _
  have hA : Uniform M (fun _ _ j=>(2^fixedAlpha m 2)^j) := hpow _
  have hB : Uniform M (fun _ _ j=>(p^(2*K))^j) := hpow _
  have hD : Uniform M (fun _ _ j=>(drift*scale)^j) := hpow _
  have h2R : Uniform M (fun _ _ j=>(2*(4^fixedLength m))^j) := hpow _
  have h2F : Uniform M (fun _ _ j=>(2*F)^j) := hpow _
  have hscale : Uniform M (fun _ _ j=>(2^(fixedPi m 2*K))^j) := hpow _
  have h9 : Uniform M (fun _ _ j=>9^j) := hpow _
  have field0 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).localSize) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalArenaPrefixFootprints.sourceWidth maps cap + ThreeSum.WeightedGlobalArenaPrefixFootprints.wantedWidth maps τ + 106))
  have field1 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).radixCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hj (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hW (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))
  have field2 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).joinCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 10) hn) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) hp)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p) hP)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)))
  have field3 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).hits) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)
  have field4 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).sourceHistogram) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hFp hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))
  have field5 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).sourceWord) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p * p)) hP)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hR)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M F)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (F * F)) hF)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M F)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p) hP))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 12) hp)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 32)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hFp hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) hA) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2))))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2))))) h2R) h2F) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 20) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p + 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p + p + 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 10))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hp (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)))) hp) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M F)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalArenaPrefixFootprints.wantedWidth maps τ))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 8) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p) hP)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (4 * p))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16))) h2R) h2F) hn) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hn) hn) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hp (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16))))
  have field6 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).prefixCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hQ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 9)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3130753934820264)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1025) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M m)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M F)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (F + 1)) hF)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1100))
  have field7 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).bankCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hFp (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))
  have field8 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).nearMetadata) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj)) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))
  have field9 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).nearDivision) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3))
  have field10 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).frontendWord) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 10000) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) hQ) hFp) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ)) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hQ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hQ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))) 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hQ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hQ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hA (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))) 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)))
  have field11 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).tensorCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) 4)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.TernaryPairedColumnEnumeration.width K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 5))
  have field12 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).tensorWord) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 2) ^ 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) 4)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) 4) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) 5)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 8))))
  have field13 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).potentialWord) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 10) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.TernaryPairedColumnEnumeration.width K + 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.TernaryPairedColumnEnumeration.width K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.TernaryPairedColumnEnumeration.width K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.TernaryPairedColumnEnumeration.width K)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryPairedPolynomial.polynomial K).coefficient.toNat) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hQ 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hW 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2))) 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.LightTernaryPairedPolynomial.polynomial K).degree)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryPairedPolynomial.polynomial K).coefficient.toNat) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hQ 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hW 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2))) 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.LightTernaryPairedPolynomial.polynomial K).degree))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.TernaryPairedColumnEnumeration.width K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryPairedPolynomial.polynomial K).coefficient.toNat) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hQ 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hW 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ 2))) 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.LightTernaryPairedPolynomial.polynomial K).degree))))
  have field14 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).spanCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hp hJ)
  have field15 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).originalMatrixCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)))
  have field16 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).menuCells) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (8 * p ^ (4 * K + 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3))) 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)))
  have field17 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).budgets) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hB (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hD (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hn)) hn) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p ^ (2 * K)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M drift)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M scale)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul h9 (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2)))
  have field18 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).depth) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hn (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 5) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))) hj) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100))
  have field19 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).reporterWord) := by
    have h2N : Uniform M (fun _ _ j=>2^(2*(fixedLength m*j)+1)) := by
      have hh := (Uniform.const M 2).mul hQ
      convert hh using 1
      funext n U j
      rw [pow_succ,show 2*(fixedLength m*j)=(2*fixedLength m)*j by ring,pow_mul]
      norm_num [pow_mul]
      ring
    dsimp only [numbers,WeightedGlobalMomentDetectorResources.coefficient,WeightedGlobalMomentDetectorResources.degree,
      WeightedGlobalMomentChannelResources.need,WeightedGlobalArenaPairMass.envelope]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M ((ThreeSum.LightMomentDeterminant.wordCoefficient H).toNat + 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (M ^ ThreeSum.WeightedGlobalArenaPairMass.base maps cap)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hn (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * ThreeSum.WeightedGlobalArenaPairMass.base maps cap + 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 ^ (2 * H)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (ThreeSum.LightMomentDeterminant.wordDegree H + 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * H + 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (M ^ ThreeSum.WeightedGlobalArenaPairMass.base maps cap)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hn (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * ThreeSum.WeightedGlobalArenaPairMass.base maps cap + 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 5)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) ((2 * H + 1) * (ThreeSum.LightMomentDeterminant.wordDegree H + 1)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalMomentChannelResources.coefficient (2 * H))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (M ^ ThreeSum.WeightedGlobalArenaPairMass.base maps cap)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hn (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * ThreeSum.WeightedGlobalArenaPairMass.base maps cap + 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hU (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) (2 * (2 * H) + 1)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) hn)) h2N) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hn) hn) hp) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 16))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) hU)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3))
  have field20 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).reporterCells) := by
    dsimp only [numbers]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * H + 1)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 4) hn)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)))
  have field21 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).candidateScore) := by
    dsimp only [numbers]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hscale (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) hZ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hW) 2) K)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (((2 * K).factorial * (2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m + 1) ^ (2 * K)) ^ 2))))
  have field22 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).prefixHeader) := by
    dsimp only [numbers,weight,WeightedGlobalMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    exact (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 106) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hj (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M m)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p)) hp) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedAlpha m 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalArenaSourceSetup.alphaRank m))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * 4 ^ ThreeSum.WeightedGlobalLocalParameters.fixedLength m))) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (3130753934820264 * m)) hj)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj))) hFp) hQ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hp (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M p))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedAlpha m 2)) hj)) hA) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalArenaSourceSetup.alphaRank m)) hj)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1)) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedLength m)) hj) hQ)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 1024) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalArenaSourceSetup.alphaRank m)) hj)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 3) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.WeightedGlobalLocalParameters.fixedAlpha m 2)) hj)))) hR) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hB (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p ^ (2 * K))))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul h9 (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 9))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hn)) hn) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p ^ (2 * K)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M drift)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M scale)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)) hD) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M drift)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M scale))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hn)) hn) hJ) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mul hn hcarry)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow hn (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.pow (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.add hJ (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 2)) (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (ThreeSum.LightTernaryInitialBudgets.determinantBound K b ^ 2))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (p ^ (2 * K)))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M drift)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M scale)) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M (2 * K))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 100)) hD) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M drift))) (ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.const M 9))))
  have result := field0.add (field1.add (field2.add (field3.add (field4.add (field5.add (field6.add (field7.add (field8.add (field9.add (field10.add (field11.add (field12.add (field13.add (field14.add (field15.add (field16.add (field17.add (field18.add (field19.add (field20.add (field21.add (field22.add (Uniform.const M 0)))))))))))))))))))))))
  convert result using 1
  funext n U j
  exact Numbers.sum_list _
end ThreeSum.WeightedGlobalArenaPrefixFootprints
