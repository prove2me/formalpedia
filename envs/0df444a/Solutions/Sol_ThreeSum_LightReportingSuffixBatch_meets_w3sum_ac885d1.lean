-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixBatch.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:26.774636+00:00
-- url     : https://prove2.me/submissions/07921efe-541e-4bbd-8fdc-ad9527ff76d1

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_getElem
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem
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
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_MaskDecode_decode_card
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
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
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
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
open ThreeSum ThreeSum.LightReportingSuffixBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixBatch
theorem _root_.solution {pMain pCell pLeaf pAddress : ℕ} (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightReportingSuffixCell.body pLeaf pAddress))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress) {μ : ℕ → ℤ}
    {W V offset sourceCut boxCut stage cardinal maskBase baseL baseR dst work B D d : ℕ} (hfit : offset + V ≤ W)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : sourceCut ≤ W) (hstage : stage ≤ W) (hdataL : baseL + (W + 1) * downsetCap W sourceCut ≤ work)
    (hdataR : baseR + (W + 1) * downsetCap W sourceCut ≤ work) (hdst : dst + downsetCap V boxCut ≤ work)
    (hmasks : maskBase + masks.length ≤ work)
    (hsepL : Apart baseL ((W + 1) * downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepR : Apart baseR ((W + 1) * downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap V boxCut))
    (hspace : work + 1 + LightPascal.tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word) (hpreL : preL.card + boxCut ≤ sourceCut)
    (hpreR : preR.card + boxCut ≤ sourceCut) (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W) (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask V cardinal m) (hcardinal : cardinal ≤ boxCut) (hd : d + W + 8 ≤ lim.depth) :
    Meets lim P pMain d
      [W, sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, cardinal,
        masks.length, maskBase, baseL, baseR, dst, work]
      μ (time W V masks.length)
      (fun _ μ' =>
        TableAt μ' dst boxCut (LightSignedLeafBatch.values μ dst masks (leafWeight hfit f g stage preL preR)) ∧
          KeptBut μ μ' work dst (downsetCap V boxCut)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv hfit μ sourceCut boxCut stage cardinal maskBase baseL baseR dst work masks preL preR f g) masks.length
      (LightReportingSuffixCell.time W V + 50) ?start ?round ?done ?bound (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame
            [(W : ℤ), sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, cardinal,
              masks.length, maskBase, baseL, baseR, dst, work, 0] =
          frame
            ([(W : ℤ), sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset,
                cardinal, masks.length, maskBase, baseL, baseR, dst, work, 0] ++
              [0])
      exact (frame_append_zeros _ 1).symm
    · intro S hS
      simp [LightSignedLeafBatch.values]
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hkept, hout⟩
    let m := masks[j]
    have hm : IsMask V cardinal m := hvalid m (List.getElem_mem hj)
    let S := decode V m
    have hScard : S.card = cardinal := by
      dsimp only [S]
      rw [decode_card hm.1, hm.2]
    have hSmask : subsetMask S = m := subsetMask_decode hm.1
    have hS : S.card ≤ boxCut := hScard.trans_le hcardinal
    have hrS := subsetRank_lt hS
    have hL : (preL ∪ liftSet hfit S).card ≤ sourceCut :=
      by
      have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreL)
    have hR : (preR ∪ liftSet hfit S).card ≤ sourceCut :=
      by
      have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreR)
    have hsourceL : LightZetaStages.StoredThrough μ' baseL sourceCut f W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL
        (by
          intro i hi₀ hi₁
          exact hkept i ⟨by omega, by omega⟩)
    have hsourceR : LightZetaStages.StoredThrough μ' baseR sourceCut g W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR
        (by
          intro i hi₀ hi₁
          exact hkept i ⟨by omega, by omega⟩)
    have hmaskread : μ' (maskBase + j) = (m : ℤ) := (hkept _ ⟨by omega, by omega⟩).trans (hseg.getElem hj)
    have hc :=
      LightReportingSuffixCell.meets (d := d + 1) hcell C hfit preL preR S f g hw hcut hstage hdataL hdataR hdst hspace
        hword hproductWord hS hL hR hf hg hsourceL hsourceR (by omega)
    rw [hScard, hSmask] at hc
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmaskread,
              LightReportingSuffixCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmaskread, LightReportingSuffixCell.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmaskread, LightReportingSuffixCell.time] <;> omega)
      on_goal -1 => (rintro res μ'' ⟨hnew, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, res, μ'', ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeep i hi.1 (by omega)).trans (hkept i hi)
    · intro T hT
      have hrT := subsetRank_lt hT
      have htake : masks.take (j + 1) = masks.take j ++ [m] := by
        simpa only [m] using List.take_succ_eq_append_getElem (l := masks) hj
      by_cases heq : T = S
      · subst T
        rw [hnew]
        simp [LightSignedLeafBatch.values, htake, hSmask]
      · have hrne : dst + subsetRank T ≠ dst + subsetRank S :=
          by
          intro hh
          exact heq (subsetRank_injective V (Nat.add_left_cancel hh))
        have hmne : subsetMask T ≠ m := by
          intro hh
          exact heq (subsetMask_injective V (hh.trans hSmask.symm))
        rw [hkeep _ (by omega) hrne, hout T hT]
        simp only [LightSignedLeafBatch.values, htake, List.mem_append, List.mem_singleton, hmne, or_false]
  case done =>
    rintro _ _ ⟨r, μ', rfl, hkept, hout⟩
    exact ⟨by simpa only [List.take_length] using hout, hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightReportingSuffixBatch
