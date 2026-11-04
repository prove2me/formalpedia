-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedController.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:09:43.297352+00:00
-- url     : https://prove2.me/submissions/137dbccc-b19f-4b3a-bc03-cc27dd01fc2d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedController_program_length
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
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
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
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
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_program_length
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_program_length
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_program_length
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
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_le
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_pos_iff
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
import Theorems.Thm_ThreeSum_LightWantedSetup_program_length
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGlobalQuarticStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_lift_span
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
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_source_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sources_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
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
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
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
attribute [local simp] ThreeSum.LightWeightedGlobalSeedController.program_length
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedController
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalSeedController
theorem _root_.solution {lim : Limits}
    {menu J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted
      work hashWork hist header leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch
      quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d n U dB dC dP tB
      tC tP newSpan seedTime spanTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ → ℤ) (flag fB fC fP : ℕ → ℤ)
    (I : ℕ → (ℕ → ℤ) → Prop) (Ready Final : (ℕ → ℤ) → Prop) (hw : (lim.space : ℤ) ≤ lim.word)
    (hFlags : flags + n ≤ lim.space) (hBs : scoreB + n ≤ lim.space) (hCs : scoreC + n ≤ lim.space)
    (hPs : scorePaired + n ≤ lim.space) (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP : ℤ) ≤ lim.word)
    (hLen : J + 2 ≤ lim.space)
    (hRow :
      menu +
          (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) *
            (J + 2) ≤
        lim.space)
    (hd : d < lim.depth) (hstart : I 0 μ)
    (hstep :
      ∀ i < n,
        ∀ ν,
          I i ν →
            Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
              LightWeightedGlobalSeedScore.entry (d + 1)
              (LightWeightedGlobalSeedScore.args menu i J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold
                Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
                leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns potentialPowers
                flags scoreB scoreC scorePaired prefixLength)
              ν seedTime (fun _ ξ => I (i + 1) ξ))
    (hread :
      ∀ ν,
        I n ν →
          (∀ i < n, ν (flags + i) = flag i ∧ |flag i| ≤ 1) ∧
            (∀ i < n, ν (scoreB + i) = fB i ∧ |fB i| ≤ U) ∧
              (∀ i < n, ν (scoreC + i) = fC i ∧ |fC i| ≤ U) ∧ (∀ i < n, ν (scorePaired + i) = fP i ∧ |fP i| ≤ U))
    (hexist : ∃ i < n, LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP i)
    (hselected :
      ∀ ν,
        I n ν →
          Meets lim (LightWeightedGlobalSeedScore.program p R S K raws words maps xl yl zl xr yr zr)
            LightWeightedGlobalSeedScore.entry (d + 1)
            (LightWeightedGlobalSeedScore.args menu
              (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) J
              catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions
              wanted work hashWork hist header leftTagged rightTagged leftWeights rightWeights tensor countOutput
              quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
            ν seedTime (fun _ ξ => Ready ξ))
    (hspan :
      ∀ ν,
        Ready ν →
          Meets lim LightStoredSpan.program 1 (d + 1)
            [catalog, catalogRows,
              menu +
                (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1) *
                  (J + 2),
              newSpan, J, p]
            ν spanTime (fun _ ξ => Final ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) entry d
      (args
        (LightWeightedGlobalSeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew
          nC Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged leftWeights
          rightWeights tensor countOutput quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC
          scorePaired prefixLength)
        n dB dC dP tB tC tP newSpan)
      μ (time n seedTime spanTime)
      (fun r ν =>
        r = (LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n : ℤ) ∧
          Final ν) :=
  by
  let good := LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP
  let chosen := LightTernaryRowSelector.pick good n
  let argv :=
    args
      (LightWeightedGlobalSeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
        Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged leftWeights rightWeights
        tensor countOutput quadScratch quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired
        prefixLength)
      n dB dC dP tB tC tP newSpan
  have hcpos : 0 < chosen := (LightTernaryRowSelector.pick_pos_iff good n).mpr hexist
  have hcle : chosen ≤ n := LightTernaryRowSelector.pick_le good n
  have hchosenExpand :
    LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n = chosen := rfl
  have hnWord : (n : ℤ) ≤ lim.word := by omega
  have hcWord : (chosen : ℤ) ≤ lim.word := by omega
  have hRow' : menu + (chosen - 1) * (J + 2) ≤ lim.space := hRow
  have hrowWord : ((menu + (chosen - 1) * (J + 2) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hRow).trans hw
  have hprodWord : ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) ≤ lim.word :=
    by
    have hprod : (chosen - 1) * (J + 2) ≤ lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hprod).trans hw
  have hprodNonneg : 0 ≤ ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) := by positivity
  have hprodNonnegFull :
    0 ≤
      ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
        ((J : ℤ) + 2) :=
    by positivity
  have hprodWordFull :
    ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
        ((J : ℤ) + 2) ≤
      lim.word :=
    by simpa only [chosen, good] using hprodWord
  have hrowWordFull :
    (menu : ℤ) +
        ((LightTernaryRowSelector.pick (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n - 1 : ℕ) : ℤ) *
          ((J : ℤ) + 2) ≤
      lim.word :=
    by exact_mod_cast (Int.ofNat_le.mpr hRow).trans hw
  have hrowIntWord : (menu : ℤ) + ((chosen - 1 : ℕ) : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast hrowWord
  have hlenWord : ((J : ℤ) + 2) ≤ lim.word := by exact_mod_cast (Int.ofNat_le.mpr hLen).trans hw
  have hmain : (program p R S K raws words maps xl yl zl xr yr zr)[entry]? = some body :=
    by
    simp only [entry, LightWeightedGlobalSeedScore.entry, program, Nat.reduceAdd]
    rw [List.getElem?_append_right (by simp)]
    simp
  apply Meets.of_body hmain
  change Ends _ _ _ _ ⟨frame argv, μ⟩ _ _
  unfold body time
  refine
    Ends.pieceThen
      (Ends.for (T := n * (seedTime + 100) + 50) (Q := Inv argv I n) (Inv argv I) n (seedTime + 80) ?start ?round ?done
        ?bound)
      ?after (hT := by
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
  case start =>
    refine ⟨0, μ, ?_, hstart⟩
    change (⟨Function.update (frame argv) 48 0, μ⟩ : State) =
      ⟨frame (argv ++ [(0 : ℤ), 0]), μ⟩
    apply congrArg (fun f : ℕ → ℤ => (⟨f, μ⟩ : State))
    rw [update_frame_setLocal]
    simp only [argv, args, LightWeightedGlobalSeedScore.args, setLocal]
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨ret, ν, rfl, hI⟩
    have hcall := (hstep i hi ν hI).append [LightTernaryRowSelector.body, body]
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args, LightWeightedGlobalSeedScore.args,
              seedArgs, LightWeightedGlobalSeedScore.entry] <;> omega)
      on_goal -1 => (rintro r ξ hnext; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp [argv, args, LightWeightedGlobalSeedScore.args, setLocal], r, ξ, ?_, hnext⟩
    simp [argv, args, LightWeightedGlobalSeedScore.args, update_frame_setLocal]
  case done => intro σ _ hI; exact hI
  case bound =>
    rintro i _ hi _ ⟨ret, ν, rfl, hI⟩
    exact ⟨True.intro, rfl⟩
  case after =>
    rintro σ ⟨ret, ν, rfl, hI⟩
    obtain ⟨hflag, hb, hc, hp⟩ := hread ν hI
    have hselector : (program p R S K raws words maps xl yl zl xr yr zr)[177]? =
        some LightTernaryRowSelector.body := by
      unfold program
      rw [List.getElem?_append_right (by simp)]
      simp
    have hsel :=
      (LightTernaryRowSelector.meets (d := d + 1)
        hselector ν flag
        fB fC fP hw hFlags hBs hCs hPs hflag hb hc hp hWord)
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
      | refine _root_.Light.Ends.callToThen (hsel _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hsel ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args, LightWeightedGlobalSeedScore.entry, chosen, good]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args, LightWeightedGlobalSeedScore.entry, chosen, good] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args, LightWeightedGlobalSeedScore.args,
              LightWeightedGlobalSeedScore.entry, chosen, good] <;> omega)
      on_goal -1 => (rintro picked ξ ⟨hpicked, hξ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
    have hpositive : (0 : ℤ) < picked := by rw [hpicked]; exact_mod_cast hcpos
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < picked) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
              LightWeightedGlobalSeedScore.args]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [argv, args, LightWeightedGlobalSeedScore.args] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
              LightWeightedGlobalSeedScore.args] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen (chosen - 1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, chosen, good, hpicked]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, chosen, good, hpicked] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, chosen, good, hpicked] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      have hs := (hselected ν hI).append [LightTernaryRowSelector.body, body]
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
        | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen, good]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen,
                  good] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, LightWeightedGlobalSeedScore.entry, chosen, good] <;> omega)
        on_goal -1 => (rintro r ξ hr; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      have hsp := LightWeightedGlobalSeedScore.lift_span p R S K raws words maps xl yl zl xr yr zr (hspan ξ hr)
      have hsp' := hsp.append [LightTernaryRowSelector.body, body]
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
        | refine _root_.Light.Ends.callToThen (hsp' _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hsp' ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, chosen, good] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good] <;> omega)
        on_goal -1 => (rintro r ζ hfinal; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen chosen ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [argv, args, LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, argv, args,
                LightWeightedGlobalSeedScore.args, seedArgs, chosen, good, hpicked] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [argv, args, LightWeightedGlobalSeedScore.args, setLocal, chosen, good], hfinal⟩
    · exact (hno hpositive).elim
end ThreeSum.LightWeightedGlobalSeedController
