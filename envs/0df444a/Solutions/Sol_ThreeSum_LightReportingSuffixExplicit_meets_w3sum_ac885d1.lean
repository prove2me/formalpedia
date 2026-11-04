-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixExplicit.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:49:10.998208+00:00
-- url     : https://prove2.me/submissions/44e922dc-9184-4433-be2e-caceae7e0c61

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
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
import Theorems.Thm_ThreeSum_ExplicitLayers_choose_le_offset
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_abs_le
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_succ
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightBlockQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_1c576168946d3ece
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2
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
import Theorems.Thm_ThreeSum_ReportingHostSuffix_leafWeight_abs_le
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_subset
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
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
open ThreeSum ThreeSum.LightReportingSuffixExplicit
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixExplicit
theorem _root_.solution {pMain pEnum pSum : ℕ} (hmain : P[pMain]? = some (body pEnum pSum)) (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W V offset cut stage t maskBase baseL baseR work B D d : ℕ} (hfit : offset + V ≤ W)
    (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ W) (hstage : stage ≤ W) (hdataL : baseL + (W + 1) * downsetCap W cut ≤ maskBase)
    (hdataR : baseR + (W + 1) * downsetCap W cut ≤ maskBase) (hmasks : maskBase + layerOffset Q.card t ≤ work)
    (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card + 1) (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut) (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B) (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W) (hd : d + W + 8 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card, subsetMask Q, t,
        baseL, baseR, maskBase, work]
      μ (time W Q.card t)
      (fun r μ' =>
        r = ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) t ∧
          KeptBut μ μ' work maskBase (layerOffset Q.card t)) :=
  by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have henumSpace : work + (2 * V + 2) ≤ lim.space :=
    by
    unfold tableSize at hspace
    nlinarith [Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2]
  have henumWord : ((2 ^ (V + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (V + 1) : ℕ) ≤ (W + 1) * 2 ^ (W + 1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hh : ((2 ^ (V + 1) : ℕ) : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh := Nat.le_mul_of_pos_left ((2 ^ stage * B) * (2 ^ stage * D)) (by omega : 0 < layerOffset Q.card t + 1)
    exact
      (by exact_mod_cast hh :
            (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤
              (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ)).trans
        haccWord
  have hweight (S : Finset (Fin V)) (hS : S ⊆ Q) :
    |leafWeight hfit f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    leafWeight_abs_le hfit f g preL preR S hstage
      ((Finset.card_le_card
            (Finset.union_subset_union (Finset.Subset.refl preL) ((liftSet_subset hfit _ _).mpr hS))).trans
        hcardL)
      ((Finset.card_le_card
            (Finset.union_subset_union (Finset.Subset.refl preR) ((liftSet_subset hfit _ _).mpr hS))).trans
        hcardR)
      hf hg
  have hacc (j : ℕ) (hj : j ≤ t) : |ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) j| ≤ lim.word :=
    by
    have hh := ExplicitLayers.valueSum_abs_le Q (leafWeight hfit f g stage preL preR) j hweight
    have hn :
      layerOffset Q.card j * ((2 ^ stage * B) * (2 ^ stage * D)) ≤
        (layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) :=
      Nat.mul_le_mul_right _ ((layerOffset_mono Q.card hj).trans (Nat.le_succ _))
    have hz :
      ((layerOffset Q.card j * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
        (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
      by exact_mod_cast hn
    exact hh.trans (hz.trans haccWord)
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
      (Ends.for (T := t * (roundTime W Q.card t + 20) + 20) (Q :=
        Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work t)
        (Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work) t (roundTime W Q.card t) ?start ?round ?done
        ?bound (hT := by
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
    simp [update_frame_setLocal]
    change
      frame
          [(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card,
            subsetMask Q, t, baseL, baseR, maskBase, work, 0, 0] =
        frame
          ([(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card,
              subsetMask Q, t, baseL, baseR, maskBase, work, 0, 0] ++
            [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨count, r, μ', rfl, hkeep⟩
    have hcap := ExplicitLayers.choose_le_offset (c := Q.card) hj
    have hEnumTime : LightQueryEnumeration.time V Q.card j ≤ 1400 * (W + 1) ^ 2 * (layerOffset Q.card t + 1) :=
      by
      have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
      have hb :=
        (LightQueryEnumeration.time_bound hQcard).trans
          (Nat.mul_le_mul_left (1400 * (V + 1) ^ 2) (Nat.succ_le_succ hcap))
      exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1400 hv))
    have hSumTime :
      LightReportingSuffixSum.time W (Q.card.choose j) ≤ 8000 * (W + 1) ^ 2 * (layerOffset Q.card t + 1) :=
      (LightReportingSuffixSum.time_bound W _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hp : 1 ≤ (W + 1) ^ 2 * (layerOffset Q.card t + 1) := Nat.mul_pos (by positivity) (by omega)
    have hround :
      LightQueryEnumeration.time V Q.card j + LightReportingSuffixSum.time W (Q.card.choose j) + 110 ≤
        roundTime W Q.card t :=
      by
      unfold roundTime
      nlinarith
    have he :=
      LightQueryEnumeration.meets (d := d + 1) (μ := μ') (t := j) (dst := maskBase) (work := work) C.enumerate C.weights
        C.leafProcs.setup.powers C.leafProcs.erase C.core Q hw henumSpace henumWord (by omega) (by omega) (by omega)
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
      first
      | refine _root_.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen he ?_ ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 =>
        (rintro newCount μ₁ ⟨hcount, hmaskSeg, _, hkeepEnum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkeep₁ : KeptBut μ μ₁ work maskBase (layerOffset Q.card t) :=
      by
      intro i hi
      exact (hkeepEnum i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩).trans (hkeep i hi)
    have hstoredL₁ :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL
        (by
          intro i _ hi
          have ha := hi.trans_le hdataL
          exact hkeep₁ i ⟨by omega, Or.inl ha⟩)
    have hstoredR₁ :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR
        (by
          intro i _ hi
          have ha := hi.trans_le hdataR
          exact hkeep₁ i ⟨by omega, Or.inl ha⟩)
    have hsumWord : (((missingSets Q j).length * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word :=
      by
      have hn := Nat.mul_le_mul_right ((2 ^ stage * B) * (2 ^ stage * D)) (hcap.trans (Nat.le_succ _))
      have hz :
        ((Q.card.choose j * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
          (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
        by exact_mod_cast hn
      simpa only [missingSets_length] using hz.trans haccWord
    have hs :=
      LightReportingSuffixSum.meets (d := d + 1) (μ := μ₁) C.sum C.leafProcs hfit Q preL preR (missingSets Q j) f g hw
        hcut hstage (by omega) (by omega) (by simpa using (show maskBase + Q.card.choose j ≤ work by omega)) hspace
        hword hproductWord hsumWord hcardL hcardR hf hg (fun U hU => (missingSets_mem Q U j).mp hU) hstoredL₁ hstoredR₁
        hmaskSeg (by omega)
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount,
              missingSets_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcount, missingSets_length] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, missingSets_length] <;> omega)
      on_goal -1 => (rintro res μ₂ ⟨hres, hkeepSum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnext := abs_le.mp (hacc (j + 1) (by omega))
    have hres' : res = ((missingSets Q j).map fun U => leafWeight hfit f g stage preL preR (Q \ U)).sum := hres
    have hsucc := ExplicitLayers.valueSum_succ Q (leafWeight hfit f g stage preL preR) j
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
        _root_.Light.Ends.setToThen (ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) (j + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsucc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres', hsucc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsucc] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, newCount, res, μ₂, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeepSum i hi.1).trans (hkeep₁ i hi)
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨count, r, μ', rfl, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨count, r, μ', rfl, hkeep⟩
    have ha := abs_le.mp (hacc t le_rfl)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) t) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hkeep⟩
end ThreeSum.LightReportingSuffixExplicit
