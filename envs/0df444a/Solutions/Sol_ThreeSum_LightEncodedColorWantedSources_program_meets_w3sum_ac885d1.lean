-- Prove2me | solution 1 for ThreeSum.LightEncodedColorWantedSources.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:23:14.295221+00:00
-- url     : https://prove2.me/submissions/d6a592cb-6497-464b-ab74-78c3bfbde702

import Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandRawA_Stored_append
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteAIndices
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteAllProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteBandPositions
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteOwnerProduct
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
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
import Theorems.Thm_ThreeSum_BlockIndexedQuery_prefixIndices_card
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
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
import Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_fin
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_outputOccurrences_representative
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_EncodedColorWantedData_header_le_nextFree
import Theorems.Thm_ThreeSum_EncodedColorWantedData_of_kept
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
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
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f4d14ad9782635c8
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_a6ca635f54b46105
import Theorems.Thm_ThreeSum_LightBandPreprocessing_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1109447aa6c56181
import Theorems.Thm_ThreeSum_LightBandRawACatalog_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4321abdf54a97fe0
import Theorems.Thm_ThreeSum_LightBandRawAColor_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Theorems.Thm_ThreeSum_LightBandRawA_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_0d1a8110a0635644
import Definitions.Def_WeightedCache3SUM_Alias_e53bbf83b76e0442
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5f0dc31657648884
import Definitions.Def_WeightedCache3SUM_Alias_a7dfb79b11046052
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Theorems.Thm_ThreeSum_LightColorArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
import Theorems.Thm_ThreeSum_LightColorBands_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Theorems.Thm_ThreeSum_LightColorClasses_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7dc97c785b0d6c4c
import Theorems.Thm_ThreeSum_LightCoverKeyData_program_meets
import Theorems.Thm_ThreeSum_LightCoverKeys_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f8e3ce9eb3f48862
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightEncodedColorFiniteSources_free_le_base
import Definitions.Def_WeightedCache3SUM_Alias_b48d986a40c8251e
import Definitions.Def_WeightedCache3SUM_Alias_f4dfed36bb9fd46e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_645c59421f5229aa
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_8622643736b2cec4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_d3fb44062fe6c749
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_0a77a2090c5d3d77
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_b5aa5d62f09c4909
import Theorems.Thm_ThreeSum_LightRawAKeys_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f8ab785e9a2d0c30
import Definitions.Def_WeightedCache3SUM_Alias_ec1662cc9a5130f8
import Definitions.Def_WeightedCache3SUM_Alias_30a2b7a89dd0955f
import Definitions.Def_WeightedCache3SUM_Alias_27ed780ce9327add
import Definitions.Def_WeightedCache3SUM_Alias_8826bf5763f0492d
import Definitions.Def_WeightedCache3SUM_Alias_f43341f6361c2b0a
import Definitions.Def_WeightedCache3SUM_Alias_e1f50da99510448e
import Definitions.Def_WeightedCache3SUM_Alias_366cab045a6bd6be
import Definitions.Def_WeightedCache3SUM_Alias_15941a0ec739ebe6
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_2968a7144f4e39f0
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_eeb26d77a562e4ce
import Definitions.Def_WeightedCache3SUM_Alias_9fe3fafc11d1cd65
import Definitions.Def_WeightedCache3SUM_Alias_43ac03e64e78764d
import Definitions.Def_WeightedCache3SUM_Alias_37fdacde3398ade3
import Definitions.Def_WeightedCache3SUM_Alias_26e627d087164e4a
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Theorems.Thm_ThreeSum_LightSourceGather_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_5dbf6f5b0c2deb9c
import Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a076d5b93ecac4d9
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
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
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Definitions.Def_WeightedCache3SUM_Alias_a24aa8421bb15a36
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
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
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BandRawA.count_zero
attribute [local simp] ThreeSum.BandRawA.firstRows_zero
attribute [local simp] ThreeSum.BandRawA.mem_finiteAIndices
attribute [local simp] ThreeSum.BandRawA.mem_finiteAllProducts
attribute [local simp] ThreeSum.BandRawA.mem_finiteBandPositions
attribute [local simp] ThreeSum.BandRawA.mem_finiteOwnerProduct
attribute [local simp] ThreeSum.BandWeightedScore.partialScore_zero
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
attribute [local simp] ThreeSum.BlockIndexedQuery.prefixIndices_card
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
attribute [local simp] ThreeSum.BlockSourceEncoding.modulus_cast
attribute [local simp] ThreeSum.BlockSourceFlags.candidateIndices_fin
attribute [local simp] ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative
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
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
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
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_card
attribute [local simp] ThreeSum.ReportingHostSuffix.liftSet_empty
attribute [local simp] ThreeSum.ReportingHostSuffix.mem_lowerSet
attribute [local simp] ThreeSum.ReportingHostSuffix.shiftEmbedding_val
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero
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
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorWantedSources
open Light Scales TrimScales BandScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
variable {lim : Limits} {d : ℕ}
namespace ThreeSum.LightEncodedColorWantedSources
theorem _root_.solution {μ : ℕ → ℤ} {a free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)}
    {hsC : C.Pairwise (· < ·)} {rA : ℤ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + depth n M xs.length ≤ lim.depth)
    (hn : 0 < n) (hp : 0 < p) (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (ha : a + xs.length ≤ free) (hav : av + n ≤ free) (hae : ae + 2 + 2 * n ≤ free) (hbv : bv + n ≤ free)
    (hbe : be + 2 + 2 * n ≤ free) (hcv : cv + n ≤ free) (hce : ce + 2 + 2 * n ≤ free)
    (htables : tables + ColorBandBounds.count n (bandSize n) ≤ free)
    (hrecords : rec + 4 * ColorBandBounds.count n (bandSize n) ≤ free)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n (bandSize n)) (bandSize n) ≤ free)
    (hspace : space free n p M U xs ≤ lim.space) (hword : (word n p M U xs.length : ℤ) ≤ lim.word) (hread : Seg μ a xs)
    (hvalues : ∀ z ∈ xs, |z| ≤ (U : ℤ)) (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H :
      SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n) originalA originalB
        originalC A B C hsA hsB hsC rA) :
    Meets lim program 180 d (args a free bv be cv ce n p M xs.length) μ (time n p M U xs)
      (fun r ν =>
        SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n) originalA
            originalB originalC A B C hsA hsB hsC rA ∧
          SourceFiniteData.Stored ν (LightEncodedColorFiniteSources.base free n p M xs) (bandSize n) p
              (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
              (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) r ∧
            LightCoverKeyData.Stored ν free (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
              LightWantedSetup.Output ν
                  (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
                  (LightGuardedWanted.left p xs)
                  (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n))) (3 * xs.length)
                  (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
                  (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n))) ∧
                M *
                      (ν
                          (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n))
                            xs.length)).toNat ≤
                    3 * xs.length * LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
                  Seg ν (LightCoverKeyData.keyEnd free (microHalf (inputBits n)) (blockCount (inputBits n)))
                      (RawAKeyLists.keys p xs) ∧
                    Kept μ ν free) :=
  by
  have hsWanted :
    LightGuardedWanted.space free p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsSource : SourceFiniteCosts.space (LightEncodedColorFiniteSources.base free n p M xs) n p U M ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwWanted :
    (LightGuardedWanted.word p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs.length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwSource : (SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hdWanted :
    d + 1 + 512 * microHalf (inputBits n) + blockCount (inputBits n) + Nat.clog 2 M + 3 * xs.length + 12 ≤ lim.depth :=
    by unfold depth at hd; omega
  have hdSource : d + 1 + 256 * mu n + 17 ≤ lim.depth := by unfold depth at hd; omega
  have hbase := LightEncodedColorFiniteSources.free_le_base free n p M xs
  have hheader :
    LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length + 4 ≤
      LightEncodedColorFiniteSources.base free n p M xs :=
    EncodedColorWantedData.header_le_nextFree ..
  apply Meets.of_body (p := 180) (by rfl : program[180]? = some (body 98 179))
  unfold body args time
  have hWanted :=
    ((LightGuardedWanted.program_meets (d := d + 1) (μ := μ) (a := a) (free := free) xs hw hp ha hsWanted hwWanted
              hdWanted hread hvalues).append
          (LightEncodedColorSources.program.map (ReportingHostRelocation.relocate 99))).append
      [body 98 179]
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
    | refine _root_.Light.Ends.callToThen (hWanted _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hWanted ?_ ?_ ?_ ?_
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
    on_goal -1 =>
      (rintro out μ₁ ⟨hout, wanted, hcount, cover, lifts, kept⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have H₁ := H.keep kept hA hB hC hav hae hbv hbe hcv hce htables hrecords hcatalog
  have hSources :=
    (ReportingHostRelocation.meets
          (LightEncodedColorFiniteSources.program_meets (d := d + 1) (μ := μ₁) (free := free) (p := p) (U := U) (M := M)
            (xs := xs) hw hdSource hn hp hA hB hC hav hae hbv hbe hcv hce htables hrecords hcatalog hsSource hwSource
            hboundB hboundC H₁ cover wanted)
          LightGuardedWanted.program).append
      [body 98 179]
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
    | refine _root_.Light.Ends.callToThen (hSources _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hSources ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightEncodedColorFiniteSources.args, hout]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightEncodedColorFiniteSources.args, hout] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightEncodedColorFiniteSources.args, hout] <;> omega)
    on_goal -1 =>
      (rintro r ν ⟨normalized, sources, cover', wanted', kept'⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨normalized, sources, cover', wanted', ?_, ?_, ?_⟩
  · dsimp only
    rw [kept' _ (by omega)]
    exact hcount
  · apply lifts.of_kept kept'
    rw [RawAKeyLists.keys_length]
    unfold LightGuardedWanted.wantedFree at hheader
    omega
  · intro q hq
    exact (kept' q (hq.trans_le hbase)).trans (kept q hq)
end ThreeSum.LightEncodedColorWantedSources
