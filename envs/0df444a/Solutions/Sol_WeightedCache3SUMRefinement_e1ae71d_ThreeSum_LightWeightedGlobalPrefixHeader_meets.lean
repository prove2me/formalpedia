-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:14:13.648187+00:00
-- url     : https://prove2.me/submissions/67456d4d-422b-4535-8fd0-0d889fff84ff

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_stores_ends
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_headerWrites_good
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_copy_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_program_length
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_meets
import Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
import Theorems.Thm_ThreeSum_LightStoredSpan_program_length
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryBudgetStep_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_digit
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_divide
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_polynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_powers
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_row
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRepeatWord_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryTensorScatter_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
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
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixLoop_prefix_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixLoop_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixSetup_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalQuarticStep_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedController_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_spanAppend_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_wanted_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withCollision_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withDivision_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScore_withWanted_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_channelLibraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_potentialLibraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_program_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_quadLibraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorHeader_args_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_args_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_libraries_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_source_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_sources_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRows_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightOriginalCollisionScore.program_length
attribute [local simp] ThreeSum.LightStoredSpan.program_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_digit
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_divide
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_polynomial
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_powers
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_row
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
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
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixLoop.prefix_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixLoop.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedController.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.spanAppend_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.wanted_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withCollision_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withDivision_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.withWanted_length
attribute [local simp]
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.channelLibraries_length
attribute [local simp]
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.potentialLibraries_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.program_main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.quadLibraries_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader.args_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.args_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.callArgs_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.libraries_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.source_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.sources_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution {lim : Limits} {P : Program}
    {main template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase d : ℕ}
    (hmain : P[main]? = some headerBody) (hcopy : P[189]? = some copyBody) (hpow : P[180]? = some LightNatPower.body)
    (hrepeat : P[190]? = some LightTernaryRepeatWord.body) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (htemplate : template + 106 ≤ live) (hlive : live + 106 ≤ hdr) (hhdr : hdr + 8 ≤ lim.space) (hd : d < lim.depth)
    (hread : Seg μ hdr [N, T, L, groups, nb, bank, powers, s]) (hF : μ (template + 99) = (Fbase : ℤ))
    (hG : μ (template + 100) = (Gbase : ℤ)) (hD : T + 2739 ≤ (2738 * (alphaRank * s) + 6 * (alpha2 * s)))
    (hN1 : (N : ℤ) + 1 ≤ lim.word)
    (hfits :
      ∀
        x ∈
          (args template live hdr s m p power alpha2 alphaRank localQ radix J ++
            locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase),
        |x| ≤ lim.word)
    (hpower : ∀ i ≤ alpha2 * s, ((2 ^ i : ℕ) : ℤ) ≤ lim.word)
    (hquery : ∀ i ≤ s, (LightTernaryRepeatWord.value localQ radix i : ℤ) ≤ lim.word) :
    Meets lim P main d (args template live hdr s m p power alpha2 alphaRank localQ radix J) μ (time s alpha2)
      (fun r ν =>
        r = ((power * p : ℕ) : ℤ) ∧
          ∃ μ₀ ret,
            (∀ i < 106, μ₀ (live + i) = μ (template + i)) ∧
              SameOutside μ μ₀ live 106 ∧
                ν =
                  Function.update
                    (patch live
                      (frame
                        (args template live hdr s m p power alpha2 alphaRank localQ radix J ++
                            locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase ++
                          [ret]))
                      μ₀ headerWrites)
                    (live + 104) 0) :=
  by
  have hbound (x : ℤ)
    (hx :
      x ∈
        args template live hdr s m p power alpha2 alphaRank localQ radix J ++
          locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase) :
    |x| ≤ lim.word := hfits x hx
  have hwN : ((N : ℕ) : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound ((N : ℕ) : ℤ) (by simp [args, locals]))
  have hwT : ((T : ℕ) : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound ((T : ℕ) : ℤ) (by simp [args, locals]))
  have hwL : ((L : ℕ) : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound ((L : ℕ) : ℤ) (by simp [args, locals]))
  have hwgroups : ((groups : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((groups : ℕ) : ℤ) (by simp [args, locals]))
  have hwnb : ((nb : ℕ) : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound ((nb : ℕ) : ℤ) (by simp [args, locals]))
  have hwbank : ((bank : ℕ) : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound ((bank : ℕ) : ℤ) (by simp [args, locals]))
  have hwpowers : ((powers : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((powers : ℕ) : ℤ) (by simp [args, locals]))
  have hwprod : ((power * p : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((power * p : ℕ) : ℤ) (by simp [args, locals]))
  have hwexp : ((alpha2 * s : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((alpha2 * s : ℕ) : ℤ) (by simp [args, locals]))
  have hwfactor : ((2 ^ (alpha2 * s) : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((2 ^ (alpha2 * s) : ℕ) : ℤ) (by simp [args, locals]))
  have hwrank : ((alphaRank * s : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((alphaRank * s : ℕ) : ℤ) (by simp [args, locals]))
  have hwstride : (((N + 1) * nb : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound (((N + 1) * nb : ℕ) : ℤ) (by simp [args, locals]))
  have hwtail : ((N * nb : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((N * nb : ℕ) : ℤ) (by simp [args, locals]))
  have hwqrank : (((2738 * (alphaRank * s) + 6 * (alpha2 * s)) : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound (((2738 * (alphaRank * s) + 6 * (alpha2 * s)) : ℕ) : ℤ) (by simp [args, locals]))
  have hwD : (((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans
      (hbound (((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 : ℕ) : ℤ) (by simp [args, locals]))
  have hwQ : ((LightTernaryRepeatWord.value localQ radix s : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((LightTernaryRepeatWord.value localQ radix s : ℕ) : ℤ) (by simp [args, locals]))
  have hwFbv : ((Fbase + N * nb : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((Fbase + N * nb : ℕ) : ℤ) (by simp [args, locals]))
  have hwGbv : ((Gbase + N * nb : ℕ) : ℤ) ≤ lim.word :=
    (le_abs_self _).trans (hbound ((Gbase + N * nb : ℕ) : ℤ) (by simp [args, locals]))
  have hS : (s : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound s (by simp [args]))
  have hQlocal : (localQ : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound localQ (by simp [args]))
  have hRadix : (radix : ℤ) ≤ lim.word := (le_abs_self _).trans (hbound radix (by simp [args]))
  have h2 : (2739 : ℤ) ≤ lim.word :=
    by
    have hc : 2739 ≤ (2738 * (alphaRank * s) + 6 * (alpha2 * s)) := by omega
    exact (Int.ofNat_le.mpr hc).trans hwqrank
  have hProd0 : (0 : ℤ) ≤ (power : ℤ) * (p : ℤ) := by positivity
  have hExp0 : (0 : ℤ) ≤ (alpha2 : ℤ) * (s : ℤ) := by positivity
  have hRank0 : (0 : ℤ) ≤ (alphaRank : ℤ) * (s : ℤ) := by positivity
  have hStride0 : (0 : ℤ) ≤ ((N : ℤ) + 1) * (nb : ℤ) := by positivity
  have hTail0 : (0 : ℤ) ≤ (N : ℤ) * (nb : ℤ) := by positivity
  have hQrank0 : (0 : ℤ) ≤ (2738 * ((alphaRank : ℤ) * (s : ℤ)) + 6 * ((alpha2 : ℤ) * (s : ℤ))) := by positivity
  have hDsub :
    ((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 : ℕ) = (2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 :=
    rfl
  have hDcast :
    (((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 : ℕ) : ℤ) =
      (2738 * ((alphaRank : ℤ) * (s : ℤ)) + 6 * ((alpha2 : ℤ) * (s : ℤ))) - (T : ℤ) - 1 :=
    by omega
  have hD0 : (0 : ℤ) ≤ (2738 * ((alphaRank : ℤ) * (s : ℤ)) + 6 * ((alpha2 : ℤ) * (s : ℤ))) - (T : ℤ) - 1 := by
    nlinarith [Int.natCast_nonneg ((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1)]
  have hDfirst : (2738 * ((alphaRank : ℤ) * (s : ℤ)) + 6 * ((alpha2 : ℤ) * (s : ℤ))) - (T : ℤ) ≤ lim.word :=
    by
    have hz : (0 : ℤ) ≤ (T : ℤ) := by positivity
    try simp only [Nat.cast_mul, Nat.cast_ofNat] at hwqrank
    omega
  push_cast at hwprod hwexp hwrank hwstride hwtail hwqrank hwFbv hwGbv
  have hc :=
    copy_meets (μ := μ) (d := d + 1) (src := template) (dst := live) (n := 106) hcopy hw (by omega) (by omega)
      (Or.inl htemplate)
  apply Meets.of_body hmain
  unfold headerBody time
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
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, LightNatPower.time,
            LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    on_goal -1 => (rintro ret μ₀ ⟨hcopied, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hr (i : ℕ) (hi : i < 8) : μ₀ (hdr + i) = μ (hdr + i) := hkept _ (Or.inr (by omega))
  have ha (i : ℕ) : ((hdr : ℤ) + (i : ℤ)).toNat = hdr + i := by omega
  have hrN : μ₀ (hdr + 0) = (N : ℤ) := by rw [hr 0 (by decide)]; simpa using hread 0 (by simp)
  have ha0 : ((hdr : ℤ) + 0).toNat = hdr + 0 := by omega
  simp only [Nat.add_zero] at hrN
  have hrT : μ₀ (hdr + 1) = (T : ℤ) := by rw [hr 1 (by decide)]; simpa using hread 1 (by simp)
  have ha1 : ((hdr : ℤ) + 1).toNat = hdr + 1 := by omega
  have hrL : μ₀ (hdr + 2) = (L : ℤ) := by rw [hr 2 (by decide)]; simpa using hread 2 (by simp)
  have ha2 : ((hdr : ℤ) + 2).toNat = hdr + 2 := by omega
  have hrgroups : μ₀ (hdr + 3) = (groups : ℤ) := by rw [hr 3 (by decide)]; simpa using hread 3 (by simp)
  have ha3 : ((hdr : ℤ) + 3).toNat = hdr + 3 := by omega
  have hrnb : μ₀ (hdr + 4) = (nb : ℤ) := by rw [hr 4 (by decide)]; simpa using hread 4 (by simp)
  have ha4 : ((hdr : ℤ) + 4).toNat = hdr + 4 := by omega
  have hrbank : μ₀ (hdr + 5) = (bank : ℤ) := by rw [hr 5 (by decide)]; simpa using hread 5 (by simp)
  have ha5 : ((hdr : ℤ) + 5).toNat = hdr + 5 := by omega
  have hrpowers : μ₀ (hdr + 6) = (powers : ℤ) := by rw [hr 6 (by decide)]; simpa using hread 6 (by simp)
  have ha6 : ((hdr : ℤ) + 6).toNat = hdr + 6 := by omega
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrN, ha0, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrN, ha0,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrN, ha0, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (T : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrT, ha1, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrT, ha1,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrT, ha1, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrL, ha2, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrL, ha2,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrL, ha2, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (groups : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrgroups, ha3, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrgroups, ha3,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrgroups, ha3, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (nb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrnb, ha4, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrnb, ha4,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrnb, ha4, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (bank : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrbank, ha5, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrbank, ha5,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrbank, ha5, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (powers : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrpowers, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrpowers, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrpowers, ha6, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (power * p : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (alpha2 * s : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
    |
      refine
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := d + 1) hpow μ₀ hwexp hpower) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := d + 1) hpow μ₀ hwexp hpower) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    on_goal -1 => (rintro factor μ₁ ⟨hfactor, hμ₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (alphaRank * s : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen ((N + 1) * nb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (N * nb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen ((2738 * (alphaRank * s) + 6 * (alpha2 * s)) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen ((2738 * (alphaRank * s) + 6 * (alpha2 * s)) - T - 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hDcast, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hDcast,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hDcast, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryRepeatWord.meets (d := d + 1) hrepeat μ₀ hQlocal hRadix hS hquery) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (LightTernaryRepeatWord.meets (d := d + 1) hrepeat μ₀ hQlocal hRadix hS hquery) ?_
          ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    on_goal -1 => (rintro query μ₂ ⟨hqueryResult, hμ₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hrf : μ₀ (template + 99) = (Fbase : ℤ) := (hkept _ (Or.inl (by omega))).trans hF
  have hrg : μ₀ (template + 100) = (Gbase : ℤ) := (hkept _ (Or.inl (by omega))).trans hG
  have hat99 : ((template : ℤ) + 99).toNat = template + 99 := by omega
  have hat100 : ((template : ℤ) + 100).toNat = template + 100 := by omega
  have hF0 : (0 : ℤ) ≤ (Fbase : ℤ) + (N : ℤ) * (nb : ℤ) := by positivity
  have hG0 : (0 : ℤ) ≤ (Gbase : ℤ) + (N : ℤ) * (nb : ℤ) := by positivity
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (Fbase + N * nb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrf, hat99, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrf, hat99,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrf, hat99, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (Gbase + N * nb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrg, hat100, LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, hrN, hrT, hrL, hrgroups, hrnb, hrbank, hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrg, hat100,
              LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, hrN, hrT, hrL, hrgroups, hrnb, hrbank,
            hrpowers, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hrg, hat100, LightNatPower.time,
            LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  let loc :=
    frame
      (args template live hdr s m p power alpha2 alphaRank localQ radix J ++
          locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase ++
        [ret])
  have hlocBase : loc 1 = (live : ℤ) := by simp [loc, args, locals]
  have hlocFit : ∀ ir ∈ headerWrites, ir.1 < 106 ∧ |loc ir.2| ≤ lim.word :=
    by
    intro ir hir
    obtain ⟨hi, hr⟩ := headerWrites_good ir hir
    refine ⟨hi, ?_⟩
    apply hfits
    have hlen :
      ir.2 <
        (args template live hdr s m p power alpha2 alphaRank localQ radix J ++
            locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase).length :=
      by simpa [args, locals] using hr
    change
      (args template live hdr s m p power alpha2 alphaRank localQ radix J ++
                locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase ++
              [ret]).getD
          ir.2 0 ∈
        _
    rw [List.getD_append _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  subst factor
  subst query
  simp only [args, locals, setLocal] at ⊢
  change Ends _ _ _ _ ⟨loc, μ₀⟩ _ _
  refine
    Ends.pieceThen (stores_ends headerWrites loc μ₀ hlocBase hw (by omega) hlocFit) ?_ (hT := by
      norm_num [headerWrites];
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
  rintro ⟨loc₁, ν⟩ ⟨hloc₁, hν⟩
  dsimp only at hloc₁
  subst loc₁
  dsimp only at hν
  subst ν
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen (live + 104) (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, loc, args, locals, headerWrites,
            LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [loc, args, locals, headerWrites, LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, loc, args, locals, headerWrites,
            LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (power * p : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, loc, args, locals, headerWrites,
            LightNatPower.time, LightTernaryRepeatWord.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [loc, args, locals, headerWrites, LightNatPower.time, LightTernaryRepeatWord.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, loc, args, locals, headerWrites,
            LightNatPower.time, LightTernaryRepeatWord.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, μ₀, ret, hcopied, hkept, rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
