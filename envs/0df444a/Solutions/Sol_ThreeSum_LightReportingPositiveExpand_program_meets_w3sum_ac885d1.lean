-- Prove2me | solution 1 for ThreeSum.LightReportingPositiveExpand.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:44:48.061797+00:00
-- url     : https://prove2.me/submissions/e04a238c-2311-4b4c-b4f5-5ea69d472f1a

import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
import Definitions.Def_Submission_ThreeSum_LightReportingPositiveExpand
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_mono_time
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
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_length_le
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Definitions.Def_WeightedCache3SUM_Alias_781f7abf8592a079
import Theorems.Thm_ThreeSum_LightReportingGather_meets
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_166ac700a68b6c71
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPositiveExpand
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingPositiveExpand
theorem _root_.solution {μ : ℕ → ℤ}
    {h J k t baseL baseR boxCut boxBase indexBase ptrBase outL outR masks dstL dstR dst selected maskBase work depth :
      ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k < J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣ (a w.1 % pMod + lift w.2.1 * pMod + shift) - globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdataL : baseL + (width h J + 1) * downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hdataR : baseR + (width h J + 1) * downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hindex : indexBase + count h (k + 1) ≤ outL) (hptr : ptrBase + count h (k + 1) ≤ outL)
    (hboxesEnd : boxBase + count h (k + 1) * stride (suffixStage J (512 * h) (k + 1)) boxCut ≤ outL)
    (houtL : outL + groupSize h ≤ outR) (houtR : outR + groupSize h ≤ masks) (hmasks : masks + groupSize h ≤ dstL)
    (hleft : dstL + groupSize h ≤ dstR) (hright : dstR + groupSize h ≤ dst) (hdst : dst + groupSize h ≤ selected)
    (hselected : selected + groupSize h ≤ maskBase)
    (hqueryMasks : maskBase + LightSparseQuery.queryItems (residualSize h J (k + 1)) t ≤ work)
    (hspace : work + 1 + tableSize (width h J) + (width h J + 1) ≤ lim.space)
    (hpowSpace : work + (2 * width h J + 2) ≤ lim.space)
    (hemodSpace :
      work + (Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h (k + 1)) + 1) + 2) ≤ lim.space)
    (hword : (((width h J + 1) * 2 ^ (width h J + 1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h (k + 1)) : ℤ) ≤ lim.word)
    (hvalueWord :
      (LightSparseQuery.magnitudeBound (suffixStage J (512 * h) (k + 1)) (suffixStage J (512 * h) (k + 1))
            (residualSize h J (k + 1)) t B.card C.card :
          ℤ) ≤
        lim.word)
    (ht : t ≤ residualSize h J (k + 1) + 1) (hboxCut : boxCut ≤ residualSize h J (k + 1))
    (hflags : residualSize h J (k + 1) - t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J) (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J) (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData :
      ∃ S : List ℤ,
        Seg μ indexBase S ∧
          S.Perm
              (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J (k + 1)) (count h (k + 1))) ∧
            S.Pairwise (· ≤ ·))
    (hptrs :
      SegN μ ptrBase
        (List.ofFn fun i : Fin (count h (k + 1)) => boxBase + i.val * stride (suffixStage J (512 * h) (k + 1)) boxCut))
    (hboxes :
      ∀ i < count h (k + 1),
        LightBoxStages.StoredThrough μ (boxBase + i * stride (suffixStage J (512 * h) (k + 1)) boxCut) boxCut
          (leafWeight (block_fit (Nat.succ_le_of_lt hk)) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
            (suffixStage J (512 * h) (k + 1)) (preL h J (k + 1) i) (preR h J (k + 1) i))
          (suffixStage J (512 * h) (k + 1)))
    (hd : depth + 2 * width h J + 16 ≤ lim.depth) :
    Meets lim program 49 depth
      [width h J, h, rowMask (outputRows w.2.2) ⟨k, hk⟩, subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows w.2.2)), masks, dstL, dstR, work, sourceCut h J,
        suffixStage J (512 * h) (k + 1), (k + 1) * h, residualSize h J (k + 1), t, baseL, baseR, boxCut, indexBase,
        ptrBase, count h (k + 1), groupSize h, dst, selected, maskBase, (k + 1) * (512 * h), outL, outR]
      μ (time h J k t)
      (fun r ν =>
        let pos := positiveChildren (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w pre hk
        r = (pos.length : ℤ) ∧
          SegN ν outL (pos.map fun next => subsetMask (leftPrefix (k + 1) (prefixRows (J := J) next))) ∧
            SegN ν outR
                (pos.map fun next => subsetMask (rightPrefix (k + 1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
              KeptOutputs μ ν masks outL outR pos.length) :=
  by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hlen :=
    LightReportingFilter.selected_length_le (fun i => prefixQuery I w (k + 1) (childAt w.2.2 pre hk i)) (groupSize h)
  change (selectedIndices I w pre hk).length ≤ groupSize h at hlen
  have hposLen : (positiveChildren I w pre hk).length = (selectedIndices I w pre hk).length := by
    simp only [positiveChildren, selectedIndices, List.length_map]
  have hmaskWord : ((2 ^ (width h J + 1) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans hword
  apply Meets.of_body (p := 49) (by rfl : program[49]? = some (body 46 48))
  unfold body time
  have he :=
    ((LightReportingCatalogExpand.program_meets (depth := depth + 1) (μ := μ) pMod shift A B C a b c w pre hk hp hkey hw
              (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hleft hright hdst hselected hqueryMasks
              hspace hpowSpace hemodSpace hword hlookupWord hvalueWord ht hboxCut hflags hstoredL hstoredR hindexData
              hptrs hboxes (by omega)).append
          (LightReportingGatherPair.program.map
            (ReportingHostRelocation.relocate LightReportingCatalogExpand.program.length))).append
      [body 46 48]
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
    | refine _root_.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen he ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingCatalogExpand.time, LightReportingGatherPair.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time] <;> omega)
    on_goal -1 =>
      (rintro found μ₁ ⟨hfound, hindices, hcounts, hchildren, hchildL, hchildR, hkeepExpand⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  change found = ((selectedIndices I w pre hk).length : ℤ) at hfound
  have htime :
    LightReportingGatherPair.time (selectedIndices I w pre hk).length ≤ LightReportingGatherPair.time (groupSize h) :=
    by
    unfold LightReportingGatherPair.time LightReportingGather.time
    omega
  have hg :=
    ((ReportingHostRelocation.meets
              (LightReportingPositiveMasks.program_meets (d := depth + 1) (μ := μ₁) (indices := selected) (srcL := dstL)
                (srcR := dstR) (dstL := outL) (dstR := outR) I w pre hk hw (by omega) (by omega) (by omega) (by omega)
                (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
                (Or.inr (by omega)) (Or.inl (by omega)) hindices hchildL hchildR hmaskWord (by omega))
              LightReportingCatalogExpand.program).append
          [body 46 48]).mono_time
      htime
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
    | refine _root_.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hfound, LightReportingCatalogExpand.time, LightReportingGatherPair.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time] <;> omega)
    on_goal -1 =>
      (rintro ret μ₂ ⟨hleftOut, hrightOut, hkeepGather⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen ((selectedIndices I w pre hk).length : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hfound, LightReportingCatalogExpand.time, LightReportingGatherPair.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, LightReportingCatalogExpand.time,
            LightReportingGatherPair.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp [I, positiveChildren, selectedIndices], hleftOut, hrightOut, ?_⟩
  intro i hi
  rw [hposLen] at hi
  exact (hkeepGather i ⟨hi.2.1, hi.2.2⟩).trans (hkeepExpand i hi.1)
end ThreeSum.LightReportingPositiveExpand
