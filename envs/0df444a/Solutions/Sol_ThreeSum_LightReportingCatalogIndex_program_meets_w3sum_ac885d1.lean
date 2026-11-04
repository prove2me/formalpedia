-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogIndex.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:28:59.619424+00:00
-- url     : https://prove2.me/submissions/2456ac18-6b93-43a3-9aa3-1a924290f200

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
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
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_166ac700a68b6c71
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_count_pos
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
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
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
import Theorems.Thm_ThreeSum_ReportingHostQueryBounds_boxStored_of_on
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
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
open ThreeSum ThreeSum.LightReportingCatalogIndex
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixOrder ReportingHostSuffix LightReportingSuffixCatalog
open LightReportingPrefixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingCatalogIndex
theorem _root_.solution {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase indexBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J * (512 * h))) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ J * (512 * h))
    (hboxCut : boxCut ≤ (J - k) * (512 * h))
    (hdataL : baseL + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤ srcS)
    (hdataR : baseR + (J * (512 * h) + 1) * downsetCap (J * (512 * h)) cut ≤ srcS)
    (hS : srcS + (512 * h).choose h ≤ pairL) (hL : pairL + LightReportingPrefixArrays.localCount (512 * h) h ≤ pairR)
    (hR : pairR + LightReportingPrefixArrays.localCount (512 * h) h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (LightReportingPrefixArrays.localCount (512 * h) h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (LightReportingPrefixArrays.localCount (512 * h) h) k ≤ ptrBase)
    (hptr : ptrBase + count h k ≤ boxBase) (hbox : boxBase + count h k * stride ((J - k) * (512 * h)) boxCut ≤ maskBase)
    (hmasks : maskBase + downsetCap ((J - k) * (512 * h)) boxCut ≤ work) (hindex : maskBase ≤ indexBase)
    (hindexEnd : indexBase + count h k ≤ work) (hpairSpace : work + 2 * (512 * h) + 2 ≤ lim.space)
    (hspace : work + 1 + tableSize (J * (512 * h)) + (J * (512 * h) + 1) ≤ lim.space)
    (hsortSpace : work + count h k ≤ lim.space) (hpowWord : ((2 ^ (512 * h + 1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2 ^ (512 * h)) (2 ^ (512 * h)) k : ℤ) ≤ lim.word)
    (hword : (((J * (512 * h) + 1) * 2 ^ (J * (512 * h) + 1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (LightReportingSortedCatalog.word (J * (512 * h)) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord :
      ((2 ^ ((J - k) * (512 * h)) * ((2 ^ ((J - k) * (512 * h)) * B) * (2 ^ ((J - k) * (512 * h)) * D)) : ℕ) : ℤ) ≤
        lim.word)
    (hpre : k * h + boxCut ≤ cut) (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J * (512 * h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J * (512 * h))) (hdPair : d + 512 * h + k + 6 ≤ lim.depth)
    (hd : d + J * (512 * h) + 15 ≤ lim.depth) (hdSort : d + Nat.clog 2 (count h k) + 3 ≤ lim.depth) :
    Meets lim program 51 d
      [J * (512 * h), cut, boxCut, (J - k) * (512 * h), (J - k) * (512 * h), k * (512 * h), baseL, baseR, 512 * h, h, k,
        srcS, pairL, pairR, stageL, stageR, ptrBase, boxBase, maskBase, work, indexBase]
      μ (time h J k boxCut)
      (fun r μ' =>
        r = (stageL + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k : ℕ) ∧
          μ' (stageL + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k) = (count h k : ℤ) ∧
            SegN μ' ptrBase
                (List.ofFn fun i : Fin (count h k) => boxBase + i.val * stride ((J - k) * (512 * h)) boxCut) ∧
              (∀ i < count h k,
                  LightBoxStages.StoredThrough μ' (boxBase + i * stride ((J - k) * (512 * h)) boxCut) boxCut
                    (leafWeight (block_fit hk) f g ((J - k) * (512 * h)) (preL h J k i) (preR h J k i))
                    ((J - k) * (512 * h))) ∧
                LightZetaStages.StoredThrough μ' baseL cut f (J * (512 * h)) ∧
                  LightZetaStages.StoredThrough μ' baseR cut g (J * (512 * h)) ∧
                    (∃ S : List ℤ,
                        Seg μ' indexBase S ∧
                          S.Perm
                              (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k)
                                (count h k)) ∧
                            S.Pairwise (· ≤ ·)) ∧
                      Kept μ μ' srcS) :=
  by
  have hn := count_pos h k
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hptrOrder : stageR ≤ ptrBase := by unfold LightRadixKeys.space at hstageR; omega
  have hprefixEndL :
    stageL + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k + 1 + count h k ≤ ptrBase :=
    hstageL.trans hptrOrder
  have hprefixEndR :
    stageR + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k + 1 + count h k ≤ ptrBase :=
    hstageR
  apply Meets.of_body (p := 51) (by rfl : program[51]? = some (body 43 50))
  unfold body time
  have hc :=
    ((LightReportingPrefixCatalog.program_meets (d := d + 1) (μ := μ) hk f g hw hcut hboxCut hdataL hdataR hS hL hR
              hstageL hstageR hptr hbox hmasks hpairSpace hspace hpowWord hkeysWord hword hvalueWord hpre hf hg hstoredL
              hstoredR (by omega) (by omega)).append
          (LightReportingSortedCatalog.program.map
            (ReportingHostRelocation.relocate LightReportingPrefixCatalog.program.length))).append
      [body 43 50]
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
    on_goal -1 =>
      (rintro head μ₁ ⟨hhead, hptrs, hboxes, hsourceL, hsourceR, hcount, hleft, hright, hkeepCatalog⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (count h k : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, hcount,
            LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead, hcount, LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, hcount, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen (LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k : ℕ) ?_
        ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead, LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen
        (stageR + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
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
    refine
      _root_.Light.Ends.setToThen
        (stageL + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead, LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hs :=
    (ReportingHostRelocation.meets
          (LightReportingSortedCatalog.program_meets (d := d + 1) (μ := μ₁) (fun i => subsetMask (preL h J k i))
            (fun i => subsetMask (preR h J k i)) hw (hprefixEndL.trans (by omega)) (hprefixEndR.trans (by omega))
            hindexEnd (by omega) hsortSpace hindexWord hleft hright (fun i _ => (subsetMask_isMask (preL h J k i)).1)
            (fun i _ => (subsetMask_isMask (preR h J k i)).1) (by omega))
          LightReportingPrefixCatalog.program).append
      [body 43 50]
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
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
    on_goal -1 => (rintro result μ₂ ⟨hindexData, hkeepIndex⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine
      _root_.Light.Ends.setToThen
        (stageL + LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512 * h) h) k : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead, LightReportingPrefixCatalog.time, LightReportingSortedCatalog.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, LightReportingPrefixCatalog.time,
            LightReportingSortedCatalog.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, hindexData, ?_⟩
  · exact (hkeepIndex _ (by omega)).trans hcount
  · intro i hi
    change μ₂ (ptrBase + i) = _
    rw [hkeepIndex _
        (by
          simpa only [List.length_ofFn, List.length_map] using
            (show ptrBase + i < indexBase
              by
              have hi' : i < count h k := by simpa only [List.length_ofFn, List.length_map] using hi
              omega))]
    exact hptrs i hi
  · intro i hi
    have hmul := Nat.mul_le_mul_right (stride ((J - k) * (512 * h)) boxCut) (show i + 1 ≤ count h k by omega)
    have hmul' :
      i * stride ((J - k) * (512 * h)) boxCut + stride ((J - k) * (512 * h)) boxCut ≤
        count h k * stride ((J - k) * (512 * h)) boxCut :=
      by simpa only [Nat.add_mul, Nat.one_mul] using hmul
    have hEnd :
      boxBase + i * stride ((J - k) * (512 * h)) boxCut +
          (((J - k) * (512 * h) + 1) * downsetCap ((J - k) * (512 * h)) boxCut) ≤
        indexBase :=
      by
      change boxBase + i * stride ((J - k) * (512 * h)) boxCut + stride ((J - k) * (512 * h)) boxCut ≤ indexBase
      omega
    exact
      ReportingHostQueryBounds.boxStored_of_on (hboxes i hi) (by intro a _ ha; exact hkeepIndex a (ha.trans_le hEnd))
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceL (by intro i _ hi; exact hkeepIndex i (by omega))
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceR (by intro i _ hi; exact hkeepIndex i (by omega))
  · intro i hi
    exact (hkeepIndex i (by omega)).trans (hkeepCatalog i hi)
end ThreeSum.LightReportingCatalogIndex
