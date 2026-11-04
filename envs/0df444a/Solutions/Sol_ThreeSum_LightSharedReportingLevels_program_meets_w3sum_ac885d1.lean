-- Prove2me | solution 1 for ThreeSum.LightSharedReportingLevels.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:41:15.076001+00:00
-- url     : https://prove2.me/submissions/31b8d4e0-550a-4c52-b165-2be90dbaf9da

import Definitions.Def_Submission_ThreeSum_LightSharedReportingCell
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLoop
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
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
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_427f455cbe093cd3
import Definitions.Def_WeightedCache3SUM_Alias_ced581dbf41e1ce0
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a2917ec7b7f9f23f
import Definitions.Def_WeightedCache3SUM_Alias_fc697fae61d94ff7
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_fb2417efddae0cb5
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Definitions.Def_WeightedCache3SUM_Alias_00b35c3259394183
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Definitions.Def_WeightedCache3SUM_Alias_0d2857ef7f97fcc6
import Definitions.Def_WeightedCache3SUM_Alias_781f7abf8592a079
import Theorems.Thm_ThreeSum_LightReportingGather_meets
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_166ac700a68b6c71
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_bfa505cca5c6af3f
import Definitions.Def_WeightedCache3SUM_Alias_9e2aececf85d8818
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_19b3e85e5c649202
import Definitions.Def_WeightedCache3SUM_Alias_16a1ef9ca6dc708f
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_all
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_zero
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
import Definitions.Def_WeightedCache3SUM_Alias_40e937d67ef507b4
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Definitions.Def_WeightedCache3SUM_Alias_1c576168946d3ece
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
import Definitions.Def_WeightedCache3SUM_Alias_9ec307913a0c2e1a
import Definitions.Def_WeightedCache3SUM_Alias_70e2e63cbf342643
import Definitions.Def_WeightedCache3SUM_Alias_fe8c98caddea3b8f
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
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
import Theorems.Thm_ThreeSum_LightSwitchDepth_meets
import Theorems.Thm_ThreeSum_LightSwitchDepth_program_meets
import Theorems.Thm_ThreeSum_LightSwitch_meets
import Theorems.Thm_ThreeSum_LightSwitch_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
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
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_card
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_mask
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_subset
import Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localRow_blockSet
import Theorems.Thm_ThreeSum_ReportingHostMasks_mem_blockSet
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_pair_scratch
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_table_scratch
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_Built_append
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_Built_empty
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_baseAt_zero
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_boxCut_le
import Definitions.Def_WeightedCache3SUM_Alias_4ca9f0cf2a6baf04
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_count_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_count_succ
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_count_zero
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_finish_baseAt
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_level_le
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_pre_cut
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_residual_le_width
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_span_mono
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_span_succ
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_span_zero
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_switch_le
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
import Theorems.Thm_ThreeSum_Switch_candidates_nonempty
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
attribute [local simp] ThreeSum.LightReportingSuffixLower.scanMask_all
attribute [local simp] ThreeSum.LightReportingSuffixLower.scanMask_zero
attribute [local simp] ThreeSum.LightReportingSuffixSum.partialSum_length
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
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_card
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_mask
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_subset
attribute [local simp] ThreeSum.ReportingHostMasks.globalChildren_length
attribute [local simp] ThreeSum.ReportingHostMasks.localChildren_length
attribute [local simp] ThreeSum.ReportingHostMasks.localRow_blockSet
attribute [local simp] ThreeSum.ReportingHostMasks.mem_blockSet
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.LightSharedReportingLevels
theorem _root_.solution {lim : Limits} {μ : ℕ → ℤ} {record base h J K baseL baseR cellL cellR B D d : ℕ}
    (f g : Finset (Fin (J * (512 * h))) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ LightSwitchDepth.depth J + 1)
    (hrecords : record + 5 * K ≤ base) (hcellL : cellL < record) (hcellR : cellR < record)
    (hdataL : baseL + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) (2 * h * J) ≤ record)
    (hdataR : baseR + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) (2 * h * J) ≤ record)
    (R : Resources lim base h J K B D d) (hf : ∀ S, S.card ≤ 2 * h * J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2 * h * J → |g S| ≤ D) (hleftRead : μ cellL = (baseL : ℤ)) (hrightRead : μ cellR = (baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL (2 * h * J) f (J * (512 * h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (2 * h * J) g (J * (512 * h))) :
    Meets lim program 64 d [h, J, K, cellL, cellR, localChoose h, localPairs h, record, base] μ (time h J K)
      (fun result ν =>
        result = (baseAt base h J K : ℤ) ∧
          Built ν record base h J K f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5 * K)) :=
  by
  have hstate := R.state
  have hspace := R.space
  have hdepth := R.widthDepth
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hKWord : (K : ℤ) ≤ lim.word := by omega
  have hJWord : (J : ℤ) ≤ lim.word := by omega
  have hconstants : (512 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body (p := 64) (by rfl : program[64]? = some (body 63 62))
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
    refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
    refine _root_.Light.Ends.setToThen (base : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (LightSharedReportingLoop.forSum (T := (∑ i ∈ Finset.range K, (roundTime h J i + 8)) + 6) (Q :=
        Inv μ record base h J K cellL cellR K f g) (Inv μ record base h J K cellL cellR · f g) K (roundTime h J) ?start
        ?round ?done ?bound hKWord
        (by
          simp only [Expr.cost]
          have hs : (∑ i ∈ Finset.range K, (1 + roundTime h J i + 7)) = ∑ i ∈ Finset.range K, (roundTime h J i + 8) :=
            by
            apply Finset.sum_congr rfl
            intro i hi
            omega
          omega))
      ?finish
  case start =>
    refine ⟨0, 0, 0, μ, ?_, Built.empty _ _ _ _ _ _ _, SameOn.refl, fun _ _ => rfl⟩
    simp only [SharedReportingBankLevels.count_zero, span_zero, baseAt_zero]
    simp [update_frame_setLocal]
    exact (frame_append_zeros [h, J, K, cellL, cellR, localChoose h, localPairs h, record, base, 1, 2, base, 0] 3).symm
  case round =>
    rintro i _ hi _ ⟨r, t, cut, ν, rfl, built, kept, keptBlock⟩
    have hiDepth : i ≤ LightSwitchDepth.depth J := by omega
    have hiJ := level_le hiDepth
    have hnext := baseAt_mono base h J (show i + 1 ≤ K by omega)
    have hcellSpace : finish (baseAt base h J i) h J i (boxCut h J i) ≤ lim.space :=
      by
      rw [finish_baseAt]
      exact hnext.trans hspace
    have hbefore := baseAt_mono base h J (show i ≤ K by omega)
    have hcurrent : baseAt base h J i ≤ lim.space := hbefore.trans hspace
    have hlocalSpace := (pair_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hwidthSpace := (table_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hW : J * (512 * h) ≤ lim.space := by omega
    have hL : 512 * h ≤ lim.space := by omega
    have hV : (J - i) * (512 * h) ≤ J * (512 * h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hrV := residual_le_width h J i
    have hrNat : residual h J i ≤ lim.space := by omega
    have hrWord : (2 : ℤ) * (h : ℤ) * ((J : ℤ) - (i : ℤ)) ≤ lim.word := by
      simpa only [SharedReportingBankLevels.residual, Nat.cast_mul, Nat.cast_sub hiJ, Nat.cast_ofNat] using
        (Int.ofNat_le.mpr hrNat).trans hw
    have hrNZ : (0 : ℤ) ≤ (2 : ℤ) * (h : ℤ) * ((J : ℤ) - (i : ℤ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Int.ofNat_le.mpr hiJ))
    have hN := count_mono h (show i + 1 ≤ K by omega)
    have hspan := span_mono h (show i + 1 ≤ K by omega)
    have hprod : (count h i : ℤ) * (localPairs h : ℤ) = (count h (i + 1) : ℤ) := by
      rw [SharedReportingBankLevels.count_succ, Nat.cast_mul]
    have hprodNZ : (0 : ℤ) ≤ (count h i : ℤ) * (localPairs h : ℤ) := by positivity
    have hspanEq := span_succ h i
    have hrecord : record + 5 * i + 5 ≤ baseAt base h J i :=
      by
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      omega
    unfold roundTime
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (residual h J i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              SharedReportingBankLevels.residual, Nat.cast_sub hiJ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [SharedReportingBankLevels.residual, Nat.cast_sub hiJ] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, SharedReportingBankLevels.residual,
              Nat.cast_sub hiJ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hs :=
      (ReportingHostRelocation.meets
            (LightSwitch.program_meets (μ := ν) (d := d + 1) hiJ (candidates_nonempty hiDepth) (R.switch i hi))
            LightSharedReportingCell.program).append
        [body 63 62]
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              SharedReportingBankLevels.residual]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [SharedReportingBankLevels.residual] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, SharedReportingBankLevels.residual] <;> omega)
      on_goal -1 => (rintro actual νt ⟨hactual, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst νt
    have hswitch := switch_le (h := h) hiDepth
    change Switch.switchIndex J i (residual h J i) ≤ residual h J i at hswitch
    have htWord : (switch h J i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hswitch.trans hrNat)).trans hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (boxCut h J i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, boxCut, switch,
              hactual]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [boxCut, switch, hactual] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, boxCut, switch, hactual] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hsourceL : LightZetaStages.StoredThrough ν baseL (2 * h * J) f (J * (512 * h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro a _ ha; exact kept a (by omega))
    have hsourceR : LightZetaStages.StoredThrough ν baseR (2 * h * J) g (J * (512 * h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro a _ ha; exact kept a (by omega))
    have hreadL : ν cellL = (baseL : ℤ) := (kept cellL hcellL).trans hleftRead
    have hreadR : ν cellR = (baseR : ℤ) := (kept cellR hcellR).trans hrightRead
    have hc :=
      ((LightSharedReportingCell.program_meets (μ := ν) (d := d + 1) (k := i) (boxCut := boxCut h J i) (baseL := baseL)
                (baseR := baseR) (cellL := cellL) (cellR := cellR) (free := baseAt base h J i) (rec := record + 5 * i)
                (B := B) (D := D) (t := switch h J i) hiJ f g hw hconstants hJWord ((boxCut_le h J i).trans hrV)
                (by omega) (by omega) (by omega) (by omega) hrecord hcellSpace R.powers (R.keys i hi) R.width
                (R.index i hi) (R.values i hi) htWord (pre_cut hiJ) hf hg hreadL hreadR hsourceL hsourceR
                (by have hh := R.pairDepth; omega) (by have hh := R.widthDepth; omega)
                (by have hh := R.sortDepth i hi; omega)).append
            (LightSwitch.program.map (ReportingHostRelocation.relocate LightSharedReportingCell.program.length))).append
        [body 63 62]
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hactual, switch]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hactual, switch] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hactual, switch] <;> omega)
      on_goal -1 =>
        (rintro next ν₁ ⟨hnextFree, hentry, _, _, hkeepCell⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (count h (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              SharedReportingBankLevels.count_succ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [SharedReportingBankLevels.count_succ] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, SharedReportingBankLevels.count_succ] <;> omega)
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
      refine _root_.Light.Ends.setToThen (prefixSpan h (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, span_succ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [span_succ] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, span_succ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, residual h J i, switch h J i, boxCut h J i, ν₁, ?_, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal, hnextFree, finish_baseAt, hactual, switch]
    · exact built.append hiJ hentry hkeepCell (by omega)
    · intro a ha
      exact (hkeepCell a ⟨by omega, Or.inl (by omega)⟩).trans (kept a ha)
    · intro a ⟨ha, houtside⟩
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      exact (hkeepCell a ⟨by omega, by rcases houtside with h | h <;> omega⟩).trans (keptBlock a ⟨ha, houtside⟩)
  case done =>
    rintro _ _ ⟨r, t, cut, ν, rfl, built, kept, keptBlock⟩
    exact ⟨r, t, cut, ν, rfl, built, kept, keptBlock⟩
  case bound =>
    rintro i _ _ _ ⟨r, t, cut, ν, rfl, _, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨r, t, cut, ν, rfl, built, kept, keptBlock⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (baseAt base h J K : ℕ) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, built, kept, keptBlock⟩
end ThreeSum.LightSharedReportingLevels
