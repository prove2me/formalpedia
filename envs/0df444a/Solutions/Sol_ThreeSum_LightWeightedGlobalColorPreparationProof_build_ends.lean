-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparationProof.build_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:32:13.605712+00:00
-- url     : https://prove2.me/submissions/bb2a5a6e-f9ca-4c27-ae36-29267145ebac

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_storeLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
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
import Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
import Theorems.Thm_ThreeSum_BlockMaskLayout_packedMasks_length
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_all
import Theorems.Thm_ThreeSum_BlockMaskLayout_prefixMask_zero
import Theorems.Thm_ThreeSum_BlockMaskLayout_rawMasks_length
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
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
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
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Theorems.Thm_ThreeSum_LightArgumentTable_stores_ends
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_84379a8b0e0ffbf1
import Definitions.Def_WeightedCache3SUM_Alias_9d1dcf23da3dbe87
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Definitions.Def_WeightedCache3SUM_Alias_3718d050d478b160
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Definitions.Def_WeightedCache3SUM_Alias_97fa2774a4e14663
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_166ac700a68b6c71
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientMatrix_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightTernaryCarryApply_meets
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_meets
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_program_length
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalRequester_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_program_length
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_left_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_Procs_right_meets
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_row_keep
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_left_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_right_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_carryLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_leftLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_program_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_rightLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_backendLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_dimensionsLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_program_length
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
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
import Theorems.Thm_ThreeSum_WeightedGlobalColorPreparationLayout_division_space
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
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
attribute [local simp] ThreeSum.BlockIndexedQuery.prefixIndices_card
attribute [local simp] ThreeSum.BlockMaskLayout.packedMasks_length
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_all
attribute [local simp] ThreeSum.BlockMaskLayout.prefixMask_zero
attribute [local simp] ThreeSum.BlockMaskLayout.rawMasks_length
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
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
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
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryColorPrelude.program_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryRequesterMatrix.program_length
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.carryLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.leftLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.program_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.rightLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.dimensionsLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.MaskUnion.scanSet_all
attribute [local simp] ThreeSum.MaskUnion.scanSet_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.missingSets_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.ReportingHostPairSegments.leftMasks_length
attribute [local simp] ThreeSum.ReportingHostPairSegments.rightMasks_length
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_empty
attribute [local simp] ThreeSum.ReportingHostSuffix.mem_lowerSet
attribute [local simp] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetTransport.reindex_map
attribute [local simp] ThreeSum.Switch.mem_candidates
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
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
namespace ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
private theorem stores_ends {lim : Limits} {P : Program} {d base offset : ℕ} (rs : List ℕ) (loc μ : ℕ → ℤ)
    (hbase : loc 18 = (base : ℤ)) (hw : (lim.space : ℤ) ≤ lim.word) (hs : base + offset + rs.length ≤ lim.space)
    (hfit : ∀ r ∈ rs, |loc r| ≤ lim.word) :
    Ends lim P d (stores offset rs) ⟨loc, μ⟩ (10 * rs.length)
      (fun σ => σ.loc = loc ∧ σ.mem = patch base loc μ offset rs) :=
  by
  induction rs generalizing μ offset with
  | nil => exact Ends.skip ⟨rfl, rfl⟩
  | cons r rs ih =>
    have hr := hfit r (by simp)
    have hr' : |loc r| ≤ lim.word := hr
    have ha : base + offset < lim.space := by simp only [List.length_cons] at hs; omega
    have haZ : (base : ℤ) + (offset : ℤ) ≤ lim.word := by exact_mod_cast (Int.ofNat_le.mpr ha.le).trans hw
    have ha0 : 0 ≤ (base : ℤ) + (offset : ℤ) := by positivity
    have haa : lim.Addr ((base : ℤ) + (offset : ℤ)) := by constructor; positivity; exact_mod_cast ha
    simp only [stores, List.length_cons]
    refine Ends.seq 10 (10 * rs.length) ?_ (by omega)
    refine
      Ends.storeLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbase] <;> omega)) (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega)))
    have hcast : ((base : ℤ) + (offset : ℤ)).toNat = base + offset := by omega
    simpa only [v, k, Expr.val, Op.eval, hbase, hcast, patch] using
      ih (offset := offset + 1) (Function.update μ (base + offset) (loc r))
        (by simp only [List.length_cons] at hs; omega) (fun r hr => hfit r (by simp [hr]))
private theorem patch_outside (base offset : ℕ) (loc μ : ℕ → ℤ) (rs : List ℕ) :
    SameOutside μ (patch base loc μ offset rs) (base + offset) rs.length := by
  induction rs generalizing μ offset with
  | nil => exact SameOutside.refl
  | cons r rs ih =>
    intro a ha
    have hh :=
      ih (offset + 1) (Function.update μ (base + offset) (loc r)) a (by simp only [List.length_cons] at ha; omega)
    exact hh.trans (Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _)
private theorem patch_read (base offset : ℕ) (loc μ : ℕ → ℤ) (rs : List ℕ) :
    Seg (patch base loc μ offset rs) (base + offset) (rs.map loc) := by
  induction rs generalizing μ offset with
  | nil => intro i hi; simp at hi
  | cons r rs ih =>
    apply seg_cons.mpr
    constructor
    · have hh := patch_outside base (offset + 1) loc (Function.update μ (base + offset) (loc r)) rs
      have h := hh (base + offset) (Or.inl (by omega))
      simpa [patch] using h
    · simpa only [patch, Nat.add_assoc] using ih (offset + 1) (Function.update μ (base + offset) (loc r))
private theorem list_abs {L : List ℤ} {U : ℕ} (H : ∀ z ∈ L, |z| ≤ (U : ℤ)) : ∀ i < L.length, |L.getD i 0| ≤ (U : ℤ) :=
  by
  intro i hi
  rw [List.getD_eq_getElem _ _ hi]
  exact H _ (List.getElem_mem hi)
private theorem rows_keep {μ ν : ℕ → ℤ} {dst n J cut : ℕ} {f : ℕ → TernarySignedReduction.Coordinate J → ℤ}
    (H : LightTernarySignedMatrix.Rows μ dst n J f) (K : Kept μ ν cut) (hs : dst + n * (J + 2) ≤ cut) :
    LightTernarySignedMatrix.Rows ν dst n J f := by
  intro i hi
  apply LightTernarySignedMatrix.row_keep (H i hi) K
  have hh := Nat.mul_le_mul_right (J + 2) (show i + 1 ≤ n by omega)
  rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
private theorem table_keep {μ ν : ℕ → ℤ} {dst J Q cut : ℕ} (H : LightTernaryCarryCodes.Table μ dst J Q)
    (K : Kept μ ν cut) (hs : dst + Q * (J + 1) ≤ cut) : LightTernaryCarryCodes.Table ν dst J Q :=
  by
  intro q hq
  have hh := Nat.mul_le_mul_right (J + 1) (show q + 1 ≤ Q by omega)
  rw [Nat.add_mul] at hh; simp only [one_mul] at hh
  refine ⟨(K _ (by omega)).trans (H q hq).1, ?_⟩
  intro j hj
  exact (K _ (by omega)).trans ((H q hq).2 j hj)
private theorem matrices_outside {μ ν : ℕ → ℤ} {free n U J radix : ℕ} {A B C : List ℤ}
    (H : Matrices μ free n U J radix A B C) (K : SameOutside μ ν (headerAt free n (width n)) 19) :
    Matrices ν free n U J radix A B C :=
  by
  have kb (a : ℕ) (ha : bMatrix free n (width n) ≤ a) : ν a = μ a := K a (Or.inr (by dsimp [bMatrix] at ha; omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases H.left i hi with ⟨hd, h0, h1⟩
    refine ⟨fun j => (kb _ (by omega)).trans (hd j), (kb _ (by omega)).trans h0, (kb _ (by omega)).trans h1⟩
  · intro i hi
    rcases H.right i hi with ⟨hd, h0, h1⟩
    have hc : bMatrix free n (width n) ≤ cMatrix free n (width n) B.length J := by unfold cMatrix; omega
    refine ⟨fun j => (kb _ (by omega)).trans (hd j), (kb _ (by omega)).trans h0, (kb _ (by omega)).trans h1⟩
  · intro q hq
    rcases H.carries q hq with ⟨h0, hd⟩
    have hc : bMatrix free n (width n) ≤ carry free n (width n) A.length B.length C.length J := by
      unfold carry cMatrix
      omega
    refine ⟨(kb _ (by omega)).trans h0, fun j hj => (kb _ (by have := Nat.zero_le (2 ^ J); omega)).trans (hd j hj)⟩
  · intro r hr
    rcases H.requesters r hr with ⟨⟨hd, h0, h1⟩, hp⟩
    have hp0 : bMatrix free n (width n) ≤ positions free n (width n) A.length B.length C.length J := by
      unfold positions carry cMatrix; omega
    have hm0 :
      positions free n (width n) A.length B.length C.length J ≤ oMatrix free n (width n) A.length B.length C.length J :=
      by unfold oMatrix; omega
    refine
      ⟨⟨fun j => (kb _ (by omega)).trans (hd j), (kb _ (by omega)).trans h0, (kb _ (by omega)).trans h1⟩,
        (kb _ (by omega)).trans hp⟩
end ThreeSum.LightWeightedGlobalColorPreparationProof
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalColorPreparationProof
theorem _root_.solution {lim : Limits} {radix n U R J q menu depth src params row free : ℕ} (μ : ℕ → ℤ) (A B C : List ℤ)
    (hb : 1 < radix) (bounds : Bounds lim radix n U J depth) (hparams : params + 19 ≤ free) (hparams9 : 9 ≤ params)
    (hspace : arenaFree free n (width n) A.length B.length C.length J U ≤ lim.space) (hR : (R : ℤ) ≤ lim.word)
    (hq : (q : ℤ) ≤ lim.word) (hmenu : (menu : ℤ) ≤ lim.word) (hUread : μ (params - 9) = (U : ℤ))
    (hRread : μ (params - 8) = (R : ℤ)) (hJread : μ (params - 7) = (J : ℤ)) (hqread : μ (params - 5) = (q : ℤ))
    (hmenuread : μ (params - 3) = (menu : ℤ)) (hbits : μ params = (Scales.inputBits n : ℤ))
    (hAread : ∀ i < A.length, μ (LightTernaryColorPrelude.av free n + i) = A.getD i 0)
    (hBread : ∀ i < B.length, μ (LightTernaryColorPrelude.bv free n + i) = B.getD i 0)
    (hCread : ∀ i < C.length, μ (LightTernaryColorPrelude.cv free n + i) = C.getD i 0) (hA : ∀ z ∈ A, |z| ≤ (U : ℤ))
    (hB : ∀ z ∈ B, |z| ≤ (U : ℤ)) (hC : ∀ z ∈ C, |z| ≤ (U : ℤ)) (ha : A.length ≤ n) (hbLen : B.length ≤ n)
    (hc : C.length ≤ n) :
    Ends lim (program radix) depth (buildBody radix)
      ⟨frame
          [src, n, params, row, free, free, LightTernaryColorPrelude.av free n, A.length,
            LightTernaryColorPrelude.bv free n, B.length, LightTernaryColorPrelude.cv free n, C.length],
        μ⟩
      (buildTime A.length B.length C.length J U)
      (fun σ => σ.loc 0 = (headerAt free n (width n) : ℤ) ∧ Built μ σ.mem free n U R J q menu radix A B C) :=
  by
  let W := width n
  let H := headerAt free n W
  let LB := bMatrix free n W
  let LC := cMatrix free n W B.length J
  let CC := carry free n W A.length B.length C.length J
  let PP := positions free n W A.length B.length C.length J
  let OO := oMatrix free n W A.length B.length C.length J
  let WW := work free n W A.length B.length C.length J
  let EE := arenaFree free n W A.length B.length C.length J U
  have hE : EE ≤ lim.space := hspace
  have hD : depth + 1 ≤ lim.depth := by have := bounds.kernelDepth; omega
  have horder :
    free ≤ H ∧
      H + 19 = LB ∧
        LB + B.length * (J + 2) = LC ∧
          LC + C.length * (J + 2) = CC ∧
            CC + 2 ^ J * (J + 1) = PP ∧ PP + A.length * 2 ^ J = OO ∧ OO + A.length * 2 ^ J * (J + 2) = WW ∧ WW ≤ EE :=
    by
    dsimp [H, LB, LC, CC, PP, OO, WW, EE, headerAt, bMatrix, cMatrix, carry, positions, oMatrix, work, arenaFree]
    omega
  have hav : LightTernaryColorPrelude.av free n + n ≤ H :=
    by
    dsimp [H, headerAt]
    unfold LightTernaryColorPrelude.av LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1
      LightTernaryColorPrelude.class0
    omega
  have hbv : LightTernaryColorPrelude.bv free n + n ≤ H :=
    by
    dsimp [H, headerAt]
    unfold LightTernaryColorPrelude.bv LightTernaryColorPrelude.ae LightTernaryColorPrelude.av
      LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0
    omega
  have hcv : LightTernaryColorPrelude.cv free n + n ≤ H :=
    by
    dsimp [H, headerAt]
    unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
      LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
      LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0
    omega
  have hdiv := WeightedGlobalColorPreparationLayout.division_space free n W A.length B.length C.length J U
  have hmatrixSpace : LightTernarySignedMatrix.space WW U ≤ lim.space := hdiv.1.trans hspace
  have hcarrySpace : LightTernaryCarryCodes.space WW (2 ^ J) ≤ lim.space := hdiv.2.trans hspace
  have hp (a : ℕ) (h : a ≤ EE) : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (h.trans hE)).trans bounds.hw
  have hH := hp H (by omega)
  have hLB := hp LB (by omega)
  have hLC := hp LC (by omega)
  have hCC := hp CC (by omega)
  have hPP := hp PP (by omega)
  have hOO := hp OO (by omega)
  have hWW := hp WW (by omega)
  have hEE := hp EE le_rfl
  have hn := hp n (by dsimp [H, headerAt] at horder; omega)
  have hW := hp W (by dsimp [H, headerAt] at horder; omega)
  have hQ : ((2 ^ J : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightTernaryCarryCodes.word LightOutputDecodeDigits.word; omega)).trans
      bounds.carryWord
  have hJ : (J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (by
            unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word
            omega)).trans
      bounds.matrixWord
  have hU : (U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (by
            unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word
            omega)).trans
      bounds.matrixWord
  have hradix : (radix : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (by
            unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word
            omega)).trans
      bounds.matrixWord
  have h2 : (2 : ℤ) ≤ lim.word := by
    have hh := hp 2 (by dsimp [EE, arenaFree]; omega)
    exact hh
  have hpow (i : ℕ) (hi : i ≤ J) : ((2 ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hQ
  have hmetadata (c : ℕ) (hc : c ≤ 9) : ((params : ℤ) - (c : ℤ)).toNat = params - c := by omega
  have hadd9 : ((params : ℤ) - 9).toNat = params - 9 := by omega
  have hadd8 : ((params : ℤ) - 8).toNat = params - 8 := by omega
  have hadd7 : ((params : ℤ) - 7).toNat = params - 7 := by omega
  have hadd5 : ((params : ℤ) - 5).toNat = params - 5 := by omega
  have hadd3 : ((params : ℤ) - 3).toNat = params - 3 := by omega
  have hmetadataSpace (c : ℕ) (hc : c ≤ 9) : params - c < lim.space := by omega
  have hWread : μ params + 1 = (W : ℤ) := by simp [hbits, W, width]
  have hQ0 : (0 : ℤ) ≤ (2 : ℤ) ^ J := by positivity
  have hAL : (A.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr ha).trans hn
  have hBL : (B.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hbLen).trans hn
  have hCL : (C.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hc).trans hn
  have hreq := hp (A.length * 2 ^ J) (by omega)
  have hcalcH : (free : ℤ) + 100 * ((n : ℤ) + (W : ℤ) + 1) ≤ lim.word := by simpa [H, headerAt] using hH
  have hcalcLC : (LB : ℤ) + (B.length : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by simpa [LC, cMatrix, LB] using hLC
  have hcalcCC : (LC : ℤ) + (C.length : ℤ) * ((J : ℤ) + 2) ≤ lim.word := by simpa [CC, carry, LC] using hCC
  have hcalcPP : (CC : ℤ) + (2 : ℤ) ^ J * ((J : ℤ) + 1) ≤ lim.word := by simpa [PP, positions, CC] using hPP
  have hcalcOO : (PP : ℤ) + (A.length : ℤ) * (2 : ℤ) ^ J ≤ lim.word := by simpa [OO, oMatrix, PP] using hOO
  have hcalcWW : (OO : ℤ) + ((A.length : ℤ) * (2 : ℤ) ^ J) * ((J : ℤ) + 2) ≤ lim.word := by
    simpa [WW, work, OO, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using hWW
  have hcalcEE : (WW : ℤ) + 100 * ((U : ℤ) + (2 : ℤ) ^ J + (J : ℤ) + 1) ≤ lim.word := by
    simpa [EE, arenaFree, WW] using hEE
  have hprodB0 : (0 : ℤ) ≤ (B.length : ℤ) * ((J : ℤ) + 2) := by positivity
  have hprodC0 : (0 : ℤ) ≤ (C.length : ℤ) * ((J : ℤ) + 2) := by positivity
  have hprodQ0 : (0 : ℤ) ≤ (2 : ℤ) ^ J * ((J : ℤ) + 1) := by positivity
  have hprodA0 : (0 : ℤ) ≤ (A.length : ℤ) * (2 : ℤ) ^ J := by positivity
  have hprodAQ0 : (0 : ℤ) ≤ ((A.length : ℤ) * (2 : ℤ) ^ J) * ((J : ℤ) + 2) := by positivity
  unfold buildBody buildTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (U : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hUread, hadd9, hmetadataSpace]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hUread, hadd9, hmetadataSpace] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hUread, hadd9, hmetadataSpace] <;> omega)
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
    refine _root_.Light.Ends.setToThen (R : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hRread, hadd8, hmetadataSpace]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hRread, hadd8, hmetadataSpace] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hRread, hadd8, hmetadataSpace] <;> omega)
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
    refine _root_.Light.Ends.setToThen (J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hJread, hadd7, hmetadataSpace]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hJread, hadd7, hmetadataSpace] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hJread, hadd7, hmetadataSpace] <;> omega)
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
    refine _root_.Light.Ends.setToThen (q : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqread, hadd5, hmetadataSpace]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hqread, hadd5, hmetadataSpace] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqread, hadd5, hmetadataSpace] <;> omega)
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
    refine _root_.Light.Ends.setToThen (menu : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmenuread, hadd3, hmetadataSpace]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmenuread, hadd3, hmetadataSpace] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmenuread, hadd3, hmetadataSpace] <;> omega)
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
    refine _root_.Light.Ends.setToThen (W : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits, hWread]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbits, hWread] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits, hWread] <;> omega)
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
    refine _root_.Light.Ends.setToThen (H : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, H, headerAt]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [H, headerAt] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, H, headerAt] <;> omega)
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
    refine _root_.Light.Ends.setToThen (LB : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LB, bMatrix, H]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LB, bMatrix, H] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LB, bMatrix, H] <;> omega)
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
    refine _root_.Light.Ends.setToThen (LC : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LC, cMatrix, LB]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LC, cMatrix, LB] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LC, cMatrix, LB] <;> omega)
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
          ((LightNatPower.meets (d := depth + 1) (show (program radix)[37]? = some LightNatPower.body from rfl) μ hJ
              hpow)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightNatPower.meets (d := depth + 1) (show (program radix)[37]? = some LightNatPower.body from rfl) μ hJ
            hpow)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro powResult νp ⟨hPow, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst νp
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (A.length * 2 ^ J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow] <;> omega)
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
    refine _root_.Light.Ends.setToThen (CC : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, CC, carry, LC]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [CC, carry, LC] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, CC, carry, LC] <;> omega)
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
    refine _root_.Light.Ends.setToThen (PP : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow, PP, positions, CC]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow, PP, positions, CC] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow, PP, positions, CC] <;> omega)
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
    refine _root_.Light.Ends.setToThen (OO : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, OO, oMatrix, PP]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [OO, oMatrix, PP] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, OO, oMatrix, PP] <;> omega)
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
    refine _root_.Light.Ends.setToThen (WW : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, WW, work, OO]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [WW, work, OO] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, WW, work, OO] <;> omega)
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
    refine _root_.Light.Ends.setToThen (EE : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, EE, arenaFree, WW, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [EE, arenaFree, WW, hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, EE, arenaFree, WW, hPow] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hleft :=
    (leftProcs radix).left_meets (d := depth + 1) (μ := μ) (src := LightTernaryColorPrelude.bv free n) (n := B.length)
      (U := U) (J := J) (radix := radix) (dst := LB) (work := WW) (fun i => B.getD i 0) bounds.hw
      (by have := bounds.kernelDepth; omega) hb.le (by omega) (by omega) hmatrixSpace bounds.matrixWord hBread
      (list_abs hB)
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
    | refine _root_.Light.Ends.callToThen (hleft _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hleft ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow] <;> omega)
    on_goal -1 => (rintro lret μL ⟨hLeft, kLeft⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hCread' : ∀ i < C.length, μL (LightTernaryColorPrelude.cv free n + i) = C.getD i 0 := by
    intro i hi
    rw [kLeft _ (by omega), hCread i hi]
  have hright :=
    (rightProcs radix).right_meets (d := depth + 1) (μ := μL) (src := LightTernaryColorPrelude.cv free n) (n :=
      C.length) (U := U) (J := J) (radix := radix) (dst := LC) (work := WW) (fun i => C.getD i 0) bounds.hw
      (by have := bounds.kernelDepth; omega) hb.le (by omega) (by omega) hmatrixSpace bounds.matrixWord hCread'
      (list_abs hC)
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
    | refine _root_.Light.Ends.callToThen (hright _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hright ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow] <;> omega)
    on_goal -1 => (rintro rret μR ⟨hRight, kRight⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcarry :=
    LightTernaryCarryCodes.meets (P := program radix) (d := depth + 1) (μ := μR) (pMain := 36) (pPower := 37) (pTable :=
      38) (pRow := 39) (pDecode := 40) (pDivide := 41) (J := J) (dst := CC) (work := WW) rfl rfl rfl rfl rfl rfl
      bounds.hw (by have := bounds.kernelDepth; omega) (by omega) hcarrySpace bounds.carryWord
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
    | refine _root_.Light.Ends.callToThen (hcarry _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcarry ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow] <;> omega)
    on_goal -1 =>
      (rintro cret μT ⟨hCarryResult, hCarries, kCarry⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hAread' : ∀ i < A.length, μT (LightTernaryColorPrelude.av free n + i) = A.getD i 0 :=
    by
    intro i hi
    rw [kCarry _ (by omega), kRight _ (by omega), kLeft _ (by omega), hAread i hi]
  have hrequest :=
    (requesterProcs radix).meets (depth := depth + 1) (src := LightTernaryColorPrelude.av free n) (n := A.length) (U :=
      U) (J := J) (radix := radix) (carry := CC) (Q := 2 ^ J) (positions := PP) (matrix := OO) (work := WW) μT
      (fun i => A.getD i 0) bounds.hw (by have := bounds.kernelDepth; omega) hb (pow_pos (by decide) _) (by omega)
      (by omega) (by omega) (by omega) hmatrixSpace bounds.matrixWord hAread' (list_abs hA) hCarries
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
    | refine _root_.Light.Ends.callToThen (hrequest _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrequest ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPow]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPow] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPow] <;> omega)
    on_goal -1 => (rintro oret μO ⟨hEntries, kRequest⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have kAll : Kept μ μO LB := by
    intro a ha
    rw [kRequest _ (by omega), kCarry _ (by omega), kRight _ (by omega), kLeft _ ha]
  have mat : Matrices μO free n U J radix A B C :=
    by
    refine ⟨?_, ?_, ?_, hEntries⟩
    ·
      exact
        rows_keep (n := B.length) (J := J) (dst := LB)
          (rows_keep (n := B.length) (J := J) (dst := LB)
            (rows_keep (n := B.length) (J := J) (dst := LB) hLeft kRight (by omega)) kCarry (by omega))
          kRequest (by omega)
    ·
      exact
        rows_keep (n := C.length) (J := J) (dst := LC)
          (rows_keep (n := C.length) (J := J) (dst := LC) hRight kCarry (by omega)) kRequest (by omega)
    · exact table_keep (J := J) (Q := 2 ^ J) (dst := CC) hCarries kRequest (by omega)
  let loc :=
    frame
      [src, n, params, row, free, free, LightTernaryColorPrelude.av free n, A.length,
        LightTernaryColorPrelude.bv free n, B.length, LightTernaryColorPrelude.cv free n, C.length, U, R, J, q, menu, W,
        H, LB, LC, OO, powResult, A.length * 2 ^ J, PP, CC, WW, EE, oret]
  have havWord := hp (LightTernaryColorPrelude.av free n) (by omega)
  have hbvWord := hp (LightTernaryColorPrelude.bv free n) (by omega)
  have hcvWord := hp (LightTernaryColorPrelude.cv free n) (by omega)
  have hloc : loc 18 = (H : ℤ) := by simp [loc]
  have hfits : ∀ r ∈ fields, |loc r| ≤ lim.word := by
    intro r hr
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals simp only [loc, frame, List.getD_cons_zero, List.getD_cons_succ, Int.natCast_nonneg, abs_of_nonneg]
    all_goals try rw [abs_of_nonneg (by positivity)]
    all_goals
      first
      | assumption
      | simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hreq
      | omega
  simp only [setLocal] at ⊢
  change Ends _ _ _ _ ⟨loc, μO⟩ _ _
  refine
    Ends.pieceThen
      (stores_ends fields loc μO hloc bounds.hw (by simpa [fields] using (show H + 19 ≤ lim.space by omega)) hfits) ?_
      (hT := by
      norm_num [fields]
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
  rintro ⟨loc', ν⟩ ⟨hloc', hν⟩
  dsimp only at hloc' hν
  subst loc'; subst ν
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (H : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, loc, fields]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [loc, fields] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, loc, fields] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a ha
    have h := patch_outside H 0 loc μO fields a (Or.inl (by simpa using ha))
    exact h.trans (kAll a (by change a < H at ha; omega))
  · have h := patch_read H 0 loc μO fields
    simpa [fields, loc, header, W, H, LB, LC, OO, PP, CC, WW, EE] using h
  · exact matrices_outside mat (by simpa [fields] using patch_outside H 0 loc μO fields)
end ThreeSum.LightWeightedGlobalColorPreparationProof
