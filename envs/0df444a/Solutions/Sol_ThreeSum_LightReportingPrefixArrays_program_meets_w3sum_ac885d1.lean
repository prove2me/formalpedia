-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixArrays.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:23:59.596623+00:00
-- url     : https://prove2.me/submissions/e4623cfb-465a-4231-ab51-2dc8b0595183

import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
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
import Theorems.Thm_ThreeSum_LayerCounts_vertex_degree_identity
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
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
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
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
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
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_bounded
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_length
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_bounded
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
open ThreeSum ThreeSum.LightReportingPrefixArrays
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingPrefixArrays
theorem _root_.solution {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hh : 2 * h ≤ L) (hS : srcS + L.choose h ≤ pairL) (hL : pairL + localCount L h ≤ pairR)
    (hR : pairR + localCount L h ≤ stageL) (hstageL : LightRadixKeys.space stageL (localCount L h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (localCount L h) k ≤ work) (hspace : work + 2 * L + 2 ≤ lim.space)
    (hpowWord : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hkeysWord : (LightRadixKeys.word (2 ^ L) (2 ^ L) k : ℤ) ≤ lim.word)
    (hd : d + L + k + 4 ≤ lim.depth) :
    Meets lim program 10 d [L, h, k, srcS, pairL, pairR, stageL, stageR, work] μ (time L h k)
      (fun r μ' =>
        r = (stageL + LightRadixKeys.offset (localCount L h) k : ℕ) ∧
          μ' (stageL + LightRadixKeys.offset (localCount L h) k) = ((localCount L h) ^ k : ℕ) ∧
            μ' (stageR + LightRadixKeys.offset (localCount L h) k) = ((localCount L h) ^ k : ℕ) ∧
              Seg μ' (stageL + LightRadixKeys.offset (localCount L h) k + 1)
                  (RadixKeyLists.values ((2 ^ L : ℕ) : ℤ) (leftMasks L h) k) ∧
                Seg μ' (stageR + LightRadixKeys.offset (localCount L h) k + 1)
                    (RadixKeyLists.values ((2 ^ L : ℕ) : ℤ) (rightMasks L h) k) ∧
                  Kept μ μ' srcS) :=
  by
  have hpos : 0 < localCount L h := Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))
  have hleftLen : (leftMasks L h).length = localCount L h := leftMasks_length L h
  have hrightLen : (rightMasks L h).length = localCount L h := rightMasks_length L h
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hworkOrder : stageR ≤ work := by unfold LightRadixKeys.space at hstageR; omega
  have hpowBound : ∀ j ≤ L + 1, ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hpairProd : L.choose h * (L - h).choose h = localCount L h := LayerCounts.vertex_degree_identity L h
  apply Meets.of_body (p := 10) (by rfl : program[10]? = some (body 7 2 8))
  unfold body time
  have hp :=
    (ReportingHostPairSegments.program_meets (d := d + 1) (μ := μ) (L := L) (h := h) (srcS := srcS) (dstL := pairL)
          (dstR := pairR) (work := work) hw hh hS (by simpa only [hpairProd] using hL) (by rw [hpairProd]; omega) hspace
          hpowWord (by omega)).append
      [LightRadixKeys.body 8 9, LightRadixRows.body 6, body 7 2 8]
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime] <;> omega)
    on_goal -1 =>
      (rintro count μ₁ ⟨hcount, hleft, hright, hkeepPair⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcount' : count = (localCount L h : ℤ) := hcount
  have hpow :=
    powTable_meets (P := program) (p := 2) (d := d + 1) (μ := μ₁) (dst := work) (L := L + 1) (b := 2) rfl hw (by omega)
      hpowBound
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime] <;> omega)
    on_goal -1 => (rintro powRet μ₂ ⟨hpowers, hkeepPowers⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadPow := powers_of_segment hpowers L le_rfl
  have hreadPowNat : μ₂ (work + L) = ((2 ^ L : ℕ) : ℤ) := by simpa using hreadPow
  have hradix := hpowBound L (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (2 ^ L : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadPow, hreadPowNat,
            LightReportingPairRows.time, LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadPow, hreadPowNat, LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadPow, hreadPowNat,
            LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hleft₂ : Seg μ₂ pairL (leftMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hleftLen] at hi; omega))]
    exact hleft i hi
  have hright₂ : Seg μ₂ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hrightLen] at hi; omega))]
    exact hright i hi
  have hl :=
    LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6) (src := pairL) (dst := stageL) (p :=
      2 ^ L) (U := 2 ^ L) rfl rfl rfl (leftMasks L h) hw (by rw [hleftLen]; omega) (by rw [hleftLen]; exact hpos)
      (leftMasks_bounded L h) k (d + 1) μ₂ (by rw [hleftLen]; exact hstageL.trans (by omega)) hkeysWord (by omega)
      hleft₂
  simp only [hleftLen] at hl
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcount', LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime] <;> omega)
    on_goal -1 =>
      (rintro leftHead μ₃ ⟨hleftHead, hleftHeader, hleftArray, hkeepLeft⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hright₃ : Seg μ₃ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepLeft _ (by rw [hrightLen] at hi; omega)]
    exact hright₂ i hi
  have hr :=
    LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6) (src := pairR) (dst := stageR) (p :=
      2 ^ L) (U := 2 ^ L) rfl rfl rfl (rightMasks L h) hw (by rw [hrightLen]; omega) (by rw [hrightLen]; exact hpos)
      (rightMasks_bounded L h) k (d + 1) μ₃ (by rw [hrightLen]; exact hstageR.trans (by omega)) hkeysWord (by omega)
      hright₃
  simp only [hrightLen] at hr
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcount', LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime] <;> omega)
    on_goal -1 =>
      (rintro rightHead μ₄ ⟨hrightHead, hrightHeader, hrightArray, hkeepRight⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hleftBound : stageL + LightRadixKeys.offset (localCount L h) k + 1 + (localCount L h) ^ k ≤ stageR := hstageL
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (stageL + LightRadixKeys.offset (localCount L h) k : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hleftHead, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hleftHead, LightReportingPairRows.time, LightRadixKeys.time, powTableTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hleftHead, LightReportingPairRows.time,
            LightRadixKeys.time, powTableTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, ?_, hrightHeader, ?_, hrightArray, ?_⟩
  · change μ₄ (stageL + LightRadixKeys.offset (localCount L h) k) = _
    rw [hkeepRight _ (by omega)]
    exact hleftHeader
  · intro i hi
    change μ₄ (stageL + LightRadixKeys.offset (localCount L h) k + 1 + i) = _
    rw [hkeepRight _ (by simp only [RadixKeyLists.values_length, hleftLen] at hi; omega)]
    exact hleftArray i hi
  · intro i hi
    exact
      (hkeepRight i (by omega)).trans
        ((hkeepLeft i (by omega)).trans ((hkeepPowers i (Or.inl (by omega))).trans (hkeepPair i hi)))
end ThreeSum.LightReportingPrefixArrays
