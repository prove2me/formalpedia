-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.prefixRows_append_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:22.36051+00:00
-- url     : https://prove2.me/submissions/26e23798-99b2-4768-8abd-7b8295fa35de

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_ThreeSum_ReportingHostMasks_mem_blockSet
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_card
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_mask
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_subset
import Theorems.Thm_ThreeSum_ReportingHostMasks_localRow_blockSet
import Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
import Theorems.Thm_Light_LocalsBut_update
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
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
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


attribute [local simp] ThreeSum.ReportingHostMasks.mem_blockSet
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_card
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_mask
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_subset
attribute [local simp] ThreeSum.ReportingHostMasks.localRow_blockSet
attribute [local simp] ThreeSum.ReportingHostMasks.globalChildren_length
attribute [local simp] ThreeSum.ReportingHostMasks.localChildren_length

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced
namespace ThreeSum.ReportingHostMasks
theorem _root_.solution {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k < J) (S : Finset (Fin L)) :
    prefixRows (J := J) (pre ++ [S]) = Function.update (prefixRows pre) ⟨k,hk⟩ S := by
  funext i
  by_cases hi : i.val < k
  · have hne : i ≠ ⟨k,hk⟩ := by
      intro he
      have hv : i.val = k := congrArg Fin.val he
      omega
    rw [Function.update_of_ne hne]
    simp only [prefixRows]
    rw [List.getElem?_append_left (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega)]
  · by_cases he : i = ⟨k,hk⟩
    · subst i
      simp [prefixRows,hp]
    · have hv : k < i.val := by
        have hn : i.val ≠ k := fun h => he (Fin.ext h)
        omega
      rw [Function.update_of_ne he]
      simp only [prefixRows]
      rw [List.getElem?_append_right (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega),hp]
      rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]
end ThreeSum.ReportingHostMasks
