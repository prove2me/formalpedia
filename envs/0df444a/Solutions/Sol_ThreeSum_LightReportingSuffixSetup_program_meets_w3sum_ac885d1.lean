-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixSetup.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:20:42.24489+00:00
-- url     : https://prove2.me/submissions/9a551087-598d-4be6-a561-65e3ee701c91

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_WeightedCache3SUM_Alias_cc1533ef8ef85837
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
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
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
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
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}
namespace ThreeSum.LightReportingSuffixSetup
theorem _root_.solution {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset + V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR + (W + 1) * downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase + (V + 1) * downsetCap V boxCut ≤ maskBase) (hmasks : maskBase + downsetCap V boxCut ≤ work)
    (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card + boxCut ≤ sourceCut) (hpreR : preR.card + boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B) (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W) (hd : d + W + 11 ≤ lim.depth) :
    Meets lim program 29 d
      [W, sourceCut, boxCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, offset, baseL, baseR,
        boxBase, maskBase, work]
      μ (time W V boxCut offset)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
          LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
            LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
              KeptBut μ μ' maskBase boxBase ((V + 1) * downsetCap V boxCut)) :=
  by
  have hpowWord (j : ℕ) (hj : j ≤ offset + 1) : ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    have hm : 2 ^ j ≤ (W + 1) * 2 ^ (W + 1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hm : ((2 ^ j : ℕ) : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body (p := 29) (by rfl : program[29]? = some (body 14 28))
  unfold body time
  have hp :=
    powTable_meets (P := program) (p := 14) (d := d + 1) (μ := μ) (dst := work) (L := offset + 1) (b := 2) rfl hw
      (by omega) hpowWord
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, coreTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, coreTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, coreTime] <;> omega)
    on_goal -1 => (rintro powRet μ₁ ⟨hpowers, hkeepPowers⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpower := powers_of_segment hpowers
  have hread : μ₁ (work + offset) = ((2 ^ offset : ℕ) : ℤ) := hpower offset le_rfl
  have hreadInt : μ₁ (work + offset) = (2 : ℤ) ^ offset := by simpa using hread
  have hpWord := hpowWord offset (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (2 ^ offset : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, hreadInt, powTableTime, coreTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hread, hreadInt, powTableTime, coreTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, hreadInt, powTableTime, coreTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hstoredL₁ :=
    LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro i _ hi; exact hkeepPowers i (Or.inl (by omega)))
  have hstoredR₁ :=
    LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro i _ hi; exact hkeepPowers i (Or.inl (by omega)))
  have hcore :=
    core_meets (d := d + 1) (μ := μ₁) hfit preL preR f g hw hcut hboxCut hstage hdataL hdataR hbox hmasks hspace hword
      hvalueWord hpreL hpreR hf hg hstoredL₁ hstoredR₁ (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcore _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcore ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, coreTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, coreTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, coreTime] <;> omega)
    on_goal -1 => (rintro res μ₂ ⟨hboxes, hL, hR, hkeepCore⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hboxes, hL, hR, ?_⟩
  intro i hi
  exact (hkeepCore i hi).trans (hkeepPowers i (Or.inl (by omega)))
end ThreeSum.LightReportingSuffixSetup
