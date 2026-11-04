-- Prove2me | solution 1 for ThreeSum.LightBlockChildrenIndexed.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:31.294429+00:00
-- url     : https://prove2.me/submissions/bee723b8-81c4-4473-b73a-eba8f0f12c93

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_mem
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_card
import Definitions.Def_WeightedCache3SUM_Alias_ae0f877763340798
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_mask
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_subset
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_subset_query
import Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_leftPrefix_step
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localRow_blockSet
import Theorems.Thm_ThreeSum_ReportingHostMasks_mem_blockSet
import Definitions.Def_WeightedCache3SUM_Alias_3945ff371f77f266
import Theorems.Thm_ThreeSum_ReportingHostMasks_prefix_disjoint_block
import Definitions.Def_WeightedCache3SUM_Alias_d254ea1907421f5c
import Theorems.Thm_ThreeSum_ReportingHostMasks_rightPrefix_step
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


namespace ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}
private theorem leftMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.leftMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,leftPrefix_step,
    blockSet_localRow _ _ ht.1]
private theorem rightMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next =>
        subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.rightMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  have he : blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩ \ localRow ⟨k,hk⟩ T) =
      blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) \ T := by
    have heT := blockSet_localRow ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) ht.1
    conv_rhs => rw [← heT]
    ext x
    obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J (512*h)).surjective x
    simp only [mem_blockSet,Finset.mem_sdiff]
    tauto
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,rightPrefix_step,he]
end ThreeSum.LightBlockChildrenIndexed
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}
namespace ThreeSum.LightBlockChildrenIndexed
theorem _root_.solution {μ : ℕ → ℤ} {h J k masks dstL dstR work d : ℕ}
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h))))
    (hp : ValidPrefix q k pre) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hmasks : masks+groupSize h ≤ dstL)
    (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ work)
    (hspace : work+(2*(J*(512*h))+2) ≤ lim.space)
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+3 ≤ lim.depth) :
    Meets lim LightBlockChildren.program 0 d
      [J*(512*h),h,rowMask (outputRows q) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows q)),masks,dstL,dstR,work]
      μ (LightBlockChildren.time (J*(512*h)) (2*h) h)
      (fun r μ' =>
        r = (subsetMask (querySet (k+1) (outputRows q)) : ℤ) ∧
        SegN μ' masks ((globalChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map subsetMask) ∧
        SegN μ' dstL ((childPrefixes q pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN μ' dstR ((childPrefixes q pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next))) ∧
        Kept μ μ' masks) := by
  have hc : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card = 2*h := by
    rw [blockSet_card]
    exact LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  have hcount : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card.choose h = groupSize h := by
    rw [hc]
    rfl
  have hcall := LightBlockChildren.program_meets (μ := μ) (d := d)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) (querySet k (outputRows q))
    hw (prefix_disjoint_block _ hk _) (prefix_disjoint_block _ hk _)
    (blockSet_subset_query _ hk) (by rw [hc]; omega)
    (hcount ▸ hmasks) (hcount ▸ hleft) (hcount ▸ hright) hspace hword hd
  have hrow : subsetMask (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) = rowMask (outputRows q) ⟨k,hk⟩ := by
    simp [rowMask]
  rw [hrow,hc,leftMasks_eq q pre hp.1 hk,rightMasks_eq q pre hp.1 hk,
    ← querySet_step (outputRows q) hk] at hcall
  exact hcall
end ThreeSum.LightBlockChildrenIndexed
