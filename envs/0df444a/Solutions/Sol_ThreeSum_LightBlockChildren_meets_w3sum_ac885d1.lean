-- Prove2me | solution 1 for ThreeSum.LightBlockChildren.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:30.230442+00:00
-- url     : https://prove2.me/submissions/611e26ef-0da3-4f0e-950c-e2eb465c5906

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
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
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff_int
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
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_mask
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_subset
import Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
import Theorems.Thm_ThreeSum_ReportingHostMasks_localRow_blockSet
import Theorems.Thm_ThreeSum_ReportingHostMasks_mask_union
import Theorems.Thm_ThreeSum_ReportingHostMasks_mem_blockSet
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
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_card
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_mask
attribute [local simp] ThreeSum.ReportingHostMasks.blockSet_subset
attribute [local simp] ThreeSum.ReportingHostMasks.globalChildren_length
attribute [local simp] ThreeSum.ReportingHostMasks.localChildren_length
attribute [local simp] ThreeSum.ReportingHostMasks.localRow_blockSet
attribute [local simp] ThreeSum.ReportingHostMasks.mem_blockSet
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
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockChildren
theorem _root_.solution {pMain pEnum pAffine : ℕ} (hmain : P[pMain]? = some (body pEnum pAffine))
    (C : Procs P pEnum pAffine) {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ} (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word) (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R) (hh : h ≤ Q.card + 1)
    (hmasks : masks + Q.card.choose h ≤ dstL) (hleft : dstL + Q.card.choose h ≤ dstR)
    (hright : dstR + Q.card.choose h ≤ work) (hspace : work + (2 * W + 2) ≤ lim.space)
    (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + W + 3 ≤ lim.depth) :
    Meets lim P pMain d [W, h, subsetMask Q, subsetMask A, subsetMask B, subsetMask R, masks, dstL, dstR, work] μ
      (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
          SegN μ' masks ((missingSets Q h).map subsetMask) ∧
            SegN μ' dstL (leftMasks A Q h) ∧ SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) :=
  by
  have hmask (S : Finset (Fin W)) : |(subsetMask S : ℤ)| ≤ lim.word :=
    by
    rw [Int.abs_natCast]
    have hs : subsetMask S ≤ 2 ^ (W + 1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hs : (subsetMask S : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hbias : (subsetMask B : ℤ) + (subsetMask Q : ℤ) = (subsetMask (B ∪ Q) : ℤ) :=
    by
    rw [mask_union _ _ hBQ]
    simp
  have hreturn := MaskDifference.subsetMask_sdiff_int R Q hQR
  have hAword := abs_le.mp (hmask A)
  have hBword := abs_le.mp (hmask B)
  have hQword := abs_le.mp (hmask Q)
  have hRword := abs_le.mp (hmask R)
  have hBiasWord := abs_le.mp (hmask (B ∪ Q))
  have hReturnWord := abs_le.mp (hmask (R \ Q))
  apply Meets.of_body hmain
  unfold body time
  have henum :=
    LightQueryEnumeration.meets (d := d + 1) (μ := μ) (dst := masks) (work := work) C.enumBody C.weightsBody
      C.powersBody C.eraseBody C.recBody Q hw hspace hword hh (by omega) (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (henum _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen henum ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryEnumeration.time,
            LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryEnumeration.time, LightReportingAffine.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryEnumeration.time,
            LightReportingAffine.time] <;>
          omega)
    on_goal -1 =>
      (rintro count μ₁ ⟨hcount, hstored, _, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (subsetMask (B ∪ Q) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbias, LightQueryEnumeration.time,
            LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbias, LightQueryEnumeration.time, LightReportingAffine.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbias, LightQueryEnumeration.time,
            LightReportingAffine.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hread₁ (i : ℕ) (hi : i < Q.card.choose h) :
    μ₁ (masks + i) = (subsetMask ((missingSets Q h)[i]'(by simpa using hi)) : ℤ) :=
    by
    have hs := hstored i (by simpa using hi)
    simpa only [List.getElem_map] using hs
  have hleftEq (i : ℕ) (hi : i < Q.card.choose h) :
    (subsetMask A : ℤ) + 1 * μ₁ (masks + i) = (subsetMask (A ∪ (missingSets Q h)[i]'(by simpa using hi)) : ℤ) :=
    by
    have ht := (missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₁ i hi, one_mul, mask_union _ _ (hAQ.mono_right ht.1)]
    simp
  have hcallL :=
    LightReportingAffine.meets (d := d + 1) (μ := μ₁) (src := masks) (dst := dstL) (n := Q.card.choose h) (b :=
      (subsetMask A : ℤ)) (c := 1) C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl hmasks))
      (by intro i hi; rw [hread₁ i hi, one_mul]; exact hmask _) (by intro i hi; rw [hleftEq i hi]; exact hmask _)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hcallL _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcallL ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryEnumeration.time,
            LightReportingAffine.time, hcount]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryEnumeration.time, LightReportingAffine.time, hcount] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryEnumeration.time,
            LightReportingAffine.time, hcount] <;>
          omega)
    on_goal -1 => (rintro retL μ₂ ⟨houtL, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hstored₂ : SegN μ₂ masks ((missingSets Q h).map subsetMask) :=
    hstored.of_sameOutside hkeepL (Or.inl (by simpa using hmasks))
  have hread₂ (i : ℕ) (hi : i < Q.card.choose h) : μ₂ (masks + i) = μ₁ (masks + i) := hkeepL _ (Or.inl (by omega))
  have hrightEq (i : ℕ) (hi : i < Q.card.choose h) :
    (subsetMask (B ∪ Q) : ℤ) + (-1) * μ₂ (masks + i) =
      (subsetMask (B ∪ (Q \ (missingSets Q h)[i]'(by simpa using hi))) : ℤ) :=
    by
    have ht := (missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₂ i hi, hread₁ i hi, ← hbias, mask_union _ _ (hBQ.mono_right Finset.sdiff_subset)]
    push_cast
    rw [← MaskDifference.subsetMask_sdiff_int _ _ ht.1]
    ring
  have hcallR :=
    LightReportingAffine.meets (d := d + 1) (μ := μ₂) (src := masks) (dst := dstR) (n := Q.card.choose h) (b :=
      (subsetMask (B ∪ Q) : ℤ)) (c := -1) C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl (by omega)))
      (by intro i hi; rw [hread₂ i hi, hread₁ i hi]; simpa using hmask ((missingSets Q h)[i]'(by simpa using hi)))
      (by intro i hi; rw [hrightEq i hi]; exact hmask _)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hcallR _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcallR ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryEnumeration.time,
            LightReportingAffine.time, hcount]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryEnumeration.time, LightReportingAffine.time, hcount] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryEnumeration.time,
            LightReportingAffine.time, hcount] <;>
          omega)
    on_goal -1 => (rintro retR μ₃ ⟨houtR, hkeepR⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (subsetMask (R \ Q) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreturn, LightQueryEnumeration.time,
            LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreturn, LightQueryEnumeration.time, LightReportingAffine.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreturn, LightQueryEnumeration.time,
            LightReportingAffine.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · exact hstored₂.of_sameOutside hkeepR (Or.inl (by simp; omega))
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [leftMasks, SegN, List.length_map, missingSets_length] using hi
    change μ₃ (dstL + i) = _
    rw [hkeepR (dstL + i) (Or.inl (by omega)), houtL i hin, hleftEq i hin]
    simp [leftMasks]
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [rightMasks, SegN, List.length_map, missingSets_length] using hi
    change μ₃ (dstR + i) = _
    rw [houtR i hin, hrightEq i hin]
    simp [rightMasks]
  · intro i hi
    exact (hkeepR i (Or.inl (by omega))).trans ((hkeepL i (Or.inl (by omega))).trans (hkeep₁ i ⟨by omega, Or.inl hi⟩))
end ThreeSum.LightBlockChildren
