-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixSum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:40.703132+00:00
-- url     : https://prove2.me/submissions/f73c338e-d972-47a8-ae83-2a2d372b2372

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_succ
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
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
import Theorems.Thm_List_abs_sum_take_map_le
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
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_succ
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_succ
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_word
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
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff_int
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
import Theorems.Thm_ThreeSum_ReportingHostSuffix_leafWeight_abs_le
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_mask_int
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_subset
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
attribute [local simp] ThreeSum.LightReportingSuffixSum.partialSum_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixSum
theorem _root_.solution {pMain pLeaf pAddress : ℕ} (hmain : P[pMain]? = some (body pLeaf))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress) {μ : ℕ → ℤ}
    {W V offset cut stage t maskBase baseL baseR work B D d : ℕ} (hfit : offset + V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (missing : List (Finset (Fin V))) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W cut ≤ work) (hdataR : baseR + (W + 1) * downsetCap W cut ≤ work)
    (hmasks : maskBase + missing.length ≤ work) (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut) (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B) (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t) (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W) (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d + W + 7 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card, subsetMask Q, t,
        missing.length, maskBase, baseL, baseR, work]
      μ (time W missing.length)
      (fun r μ' => r = (missing.map (term hfit Q preL preR f g stage)).sum ∧ Kept μ μ' work) :=
  by
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hMaskWord (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word :=
    by
    have hp : subsetMask S ≤ (W + 1) * 2 ^ (W + 1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hLocalMaskWord (S : Finset (Fin V)) : (subsetMask S : ℤ) ≤ lim.word :=
    by
    have hp : subsetMask S ≤ (V + 1) * 2 ^ (V + 1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact
      (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((V + 1) * 2 ^ (V + 1) : ℕ) : ℤ)).trans
        (LightReportingSuffixCell.small_word (by omega : V ≤ W) hword)
  have hQmask := hLocalMaskWord Q
  have hflagsL (U : Finset (Fin V)) : (preL ∪ liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card
          (Finset.union_subset_union (Finset.Subset.refl preL)
            ((liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans
      hcardL
  have hflagsR (U : Finset (Fin V)) : (preR ∪ liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card
          (Finset.union_subset_union (Finset.Subset.refl preR)
            ((liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans
      hcardR
  have htermBound :
    ∀ U ∈ missing, |term hfit Q preL preR f g stage U| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    intro U _
    exact leafWeight_abs_le hfit f g preL preR _ hstage (hflagsL U) (hflagsR U) hf hg
  have hacc (j : ℕ) : |partialSum hfit Q preL preR f g stage missing j| ≤ lim.word :=
    by
    have hh := List.abs_sum_take_map_le missing (term hfit Q preL preR f g stage) htermBound j
    exact hh.trans (by simpa only [Nat.cast_mul] using haccWord)
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := missing.length * (LightSignedLeafGeneral.time W + 90) + 20) (Q :=
        Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work missing.length)
        (Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work) missing.length
        (LightSignedLeafGeneral.time W + 80) ?start ?round ?done ?bound (hT := by
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
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, 0, μ, ?_, SameOn.refl⟩
    simp [update_frame_setLocal, partialSum]
    change
      frame
          [(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card,
            subsetMask Q, t, missing.length, maskBase, baseL, baseR, work, 0, 0] =
        frame
          ([(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card,
              subsetMask Q, t, missing.length, maskBase, baseL, baseR, work, 0, 0] ++
            [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨mask, r, μ', rfl, hkeep⟩
    let U := missing[j]
    have hu := hvalid U (List.getElem_mem hj)
    have hstoredL' :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro i _ hi; exact hkeep i (hi.trans_le hdataL))
    have hstoredR' :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro i _ hi; exact hkeep i (hi.trans_le hdataR))
    have hmask : μ' (maskBase + j) = (subsetMask U : ℤ) :=
      by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkeep _ (by omega)).trans hr
    have hcard : (Q \ U).card = Q.card - t := by rw [Finset.card_sdiff_of_subset hu.1, hu.2]
    have hmaskSub := MaskDifference.subsetMask_sdiff_int Q U hu.1
    have hcardInt : (Q.card : ℤ) - (t : ℤ) = ((Q \ U).card : ℤ) := by
      rw [hcard, Int.ofNat_sub (by rw [← hu.2]; exact Finset.card_le_card hu.1)]
    have hscaled :
      ((subsetMask Q : ℤ) - (subsetMask U : ℤ)) * (2 : ℤ) ^ offset = (subsetMask (liftSet hfit (Q \ U)) : ℤ) :=
      by
      rw [hmaskSub, liftSet_mask_int]
      push_cast
      ring
    have hlocalWord := hLocalMaskWord (Q \ U)
    have hScaledBounds :
      -lim.word ≤ ((subsetMask Q : ℤ) - (subsetMask U : ℤ)) * (2 : ℤ) ^ offset ∧
        ((subsetMask Q : ℤ) - (subsetMask U : ℤ)) * (2 : ℤ) ^ offset ≤ lim.word :=
      by
      rw [hscaled]
      have := hMaskWord (liftSet hfit (Q \ U))
      have := Int.natCast_nonneg (subsetMask (liftSet hfit (Q \ U)))
      omega
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (subsetMask (liftSet hfit (Q \ U)) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, hscaled,
              LightSignedLeafGeneral.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmask, hscaled, LightSignedLeafGeneral.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, hscaled,
              LightSignedLeafGeneral.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hc :=
      LightSignedLeafGeneral.meets (d := d + 1) C.leaf C.union C.lookup C.sign C.size C.address C.setup C.offset C.erase
        preL preR (liftSet hfit (Q \ U)) f g hw hcut hstage hdataL hdataR hspace hword hproductWord (hflagsL U)
        (hflagsR U) hf hg hstoredL' hstoredR' (by omega)
    rw [liftSet_card] at hc
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcardInt,
              LightSignedLeafGeneral.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcardInt, LightSignedLeafGeneral.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcardInt, LightSignedLeafGeneral.time] <;> omega)
      on_goal -1 => (rintro res μ₁ ⟨hres, hnewKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnext := abs_le.mp (hacc (j + 1))
    have hsum :
      partialSum hfit Q preL preR f g stage missing j + term hfit Q preL preR f g stage U =
        partialSum hfit Q preL preR f g stage missing (j + 1) :=
      (partialSum_succ hfit Q preL preR f g stage missing hj).symm
    have hres' : res = term hfit Q preL preR f g stage U := hres
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (partialSum hfit Q preL preR f g stage missing (j + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsum,
              LightSignedLeafGeneral.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres', hsum, LightSignedLeafGeneral.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsum, LightSignedLeafGeneral.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, (subsetMask (liftSet hfit (Q \ U)) : ℤ), res, μ₁, ?_, hkeep.trans hnewKeep⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨mask, r, μ', rfl, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨mask, r, μ', rfl, hkeep⟩
    have ha := abs_le.mp (hacc missing.length)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((missing.map (term hfit Q preL preR f g stage)).sum) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, partialSum_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [partialSum_length] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, partialSum_length] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hkeep⟩
end ThreeSum.LightReportingSuffixSum
