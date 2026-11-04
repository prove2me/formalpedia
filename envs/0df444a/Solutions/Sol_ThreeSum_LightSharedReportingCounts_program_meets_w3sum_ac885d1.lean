-- Prove2me | solution 1 for ThreeSum.LightSharedReportingCounts.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:12:41.894091+00:00
-- url     : https://prove2.me/submissions/6b761415-3728-4976-94a1-bedbf6207e15

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Definitions.Def_Submission_ThreeSum_LightSharedReportingCounts
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_4eb33ef6f1e27fd8
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_all
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_zero
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
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
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_length
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
open ThreeSum ThreeSum.LightSharedReportingCounts
open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout
set_option maxHeartbeats 1700000
set_option maxRecDepth 9000
namespace ThreeSum.LightSharedReportingCounts
theorem _root_.solution {lim : Limits} {μ : ℕ → ℤ} {h dst work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (horder : dst + 2 ≤ work) (hconstants : (512 : ℤ) ≤ lim.word) (hspace : work + tableSize (512 * h) ≤ lim.space)
    (hpowWord : ((2 ^ (512 * h + 1) : ℕ) : ℤ) ≤ lim.word) (hcountWord : (localPairs h : ℤ) ≤ lim.word)
    (hd : d + 512 * h + 3 ≤ lim.depth) :
    Meets lim program 0 d [h, dst, work] μ (time h)
      (fun r ν => r = (localPairs h : ℤ) ∧ SegN ν dst [localChoose h, localPairs h] ∧ Kept μ ν dst) :=
  by
  have hh : h ≤ 512 * h := by omega
  have h2h : 2 * h ≤ 512 * h := by omega
  have hstride : 512 * h + 1 ≤ tableSize (512 * h) := by unfold tableSize; nlinarith
  have hL : 512 * h ≤ lim.space := by omega
  have hlocal : localChoose h ≤ 2 ^ (512 * h + 1) :=
    (Nat.choose_le_two_pow (512 * h) h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hchoose2 : (512 * h).choose (2 * h) ≤ 2 ^ (512 * h + 1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsplit : (2 * h).choose h ≤ 2 ^ (512 * h + 1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  apply Meets.of_body (p := 0) (by rfl : program[0]? = some (body 1))
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
    refine _root_.Light.Ends.setToThen (512 * h : ℕ) ?_ ?_ ?_
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((build_meets (P := program) (pBuild := 1) (pFill := 2) (pRow := 3) (pLinear := 4) (d := d + 1) (dst := work)
              (L := 512 * h) rfl rfl rfl rfl hw (by omega) hspace hpowWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (build_meets (P := program) (pBuild := 1) (pFill := 2) (pRow := 3) (pLinear := 4) (d := d + 1) (dst := work)
            (L := 512 * h) rfl rfl rfl rfl hw (by omega) hspace hpowWord)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro result ν₁ ⟨htable, hkeepBuild⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadH := htable (512 * h) le_rfl h hh
  have hreadE₁ := htable (512 * h) le_rfl (2 * h) h2h
  have hreadE₂ := htable (2 * h) h2h h (by omega)
  have hcellH := cell_offset_lt (show 512 * h ≤ 512 * h from le_rfl) hh
  have hcellE₁ := cell_offset_lt (show 512 * h ≤ 512 * h from le_rfl) h2h
  have hcellE₂ := cell_offset_lt h2h hh
  have hrowNZ : (0 : ℤ) ≤ 512 * (h : ℤ) * (512 * (h : ℤ) + 1) := by positivity
  have hrowAddr : (work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work + 512 * h * (512 * h + 1) + 2 * h < lim.space by omega)
  have hgroupNZ : (0 : ℤ) ≤ 2 * (h : ℤ) * (512 * (h : ℤ) + 1) := by positivity
  have hgroupAddr : (work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work + 2 * h * (512 * h + 1) + h < lim.space by omega)
  have hprod : ((512 * h).choose (2 * h) : ℤ) * ((2 * h).choose h : ℤ) = (localPairs h : ℤ) := by
    simp only [localPairs, localWidth, LightReportingPrefixArrays.localCount, Nat.cast_mul]
  have hprodNZ : (0 : ℤ) ≤ ((512 * h).choose (2 * h) : ℤ) * ((2 * h).choose h : ℤ) := by positivity
  have haH :
    ((work : ℤ) + (512 * (h : ℤ)) * (512 * (h : ℤ) + 1) + (h : ℤ)).toNat = work + (512 * h) * (512 * h + 1) + h :=
    by
    have he :
      (work : ℤ) + (512 * (h : ℤ)) * (512 * (h : ℤ) + 1) + (h : ℤ) = ((work + (512 * h) * (512 * h + 1) + h : ℕ) : ℤ) :=
      by push_cast; ring
    rw [he, Int.toNat_natCast]
  have haE₁ :
    ((work : ℤ) + (512 * (h : ℤ)) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ)).toNat =
      work + (512 * h) * (512 * h + 1) + 2 * h :=
    by
    have he :
      (work : ℤ) + (512 * (h : ℤ)) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) =
        ((work + (512 * h) * (512 * h + 1) + 2 * h : ℕ) : ℤ) :=
      by push_cast; ring
    rw [he, Int.toNat_natCast]
  have haE₂ : ((work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ)).toNat = work + 2 * h * (512 * h + 1) + h :=
    by
    have he : (work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ) = ((work + 2 * h * (512 * h + 1) + h : ℕ) : ℤ) :=
      by push_cast; ring
    rw [he, Int.toNat_natCast]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (localChoose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadH, haH, localChoose, localWidth,
            buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadH, haH, localChoose, localWidth, buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadH, haH, localChoose, localWidth, buildTime,
            rowTime, LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen ((512 * h).choose (2 * h) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadE₁, haE₁, buildTime, rowTime,
            LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadE₁, haE₁, buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadE₁, haE₁, buildTime, rowTime,
            LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen ((2 * h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadE₂, haE₂, buildTime, rowTime,
            LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadE₂, haE₂, buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadE₂, haE₂, buildTime, rowTime,
            LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (localPairs h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, localPairs, localWidth,
            LightReportingPrefixArrays.localCount, buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [localPairs, localWidth, LightReportingPrefixArrays.localCount, buildTime, rowTime,
              LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, localPairs, localWidth,
            LightReportingPrefixArrays.localCount, buildTime, rowTime, LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.storeToThen dst (localChoose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (dst + 1) (localPairs h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (localPairs h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, ?_, ?_⟩
  · intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> simp [SegN]
  · intro a ha
    change Function.update (Function.update ν₁ dst (localChoose h : ℤ)) (dst + 1) (localPairs h : ℤ) a = μ a
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hkeepBuild a (Or.inl (by omega))
end ThreeSum.LightSharedReportingCounts
