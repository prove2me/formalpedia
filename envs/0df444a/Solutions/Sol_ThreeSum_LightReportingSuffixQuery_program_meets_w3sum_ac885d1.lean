-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixQuery.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:38.676333+00:00
-- url     : https://prove2.me/submissions/81f6df6e-cc8b-48d4-a232-812fa8daae9b

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQuery
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
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
import Theorems.Thm_ThreeSum_ExplicitLayers_sparse_identity
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
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_space
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_small_word
import Definitions.Def_WeightedCache3SUM_Alias_19b3e85e5c649202
import Definitions.Def_WeightedCache3SUM_Alias_1c576168946d3ece
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
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
import Theorems.Thm_ThreeSum_ReportingHostQueryBounds_boxStored_of_on
import Theorems.Thm_ThreeSum_ReportingHostSuffix_leafWeight_abs_le
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_query_eq_local_signed_sum
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
open ThreeSum ThreeSum.LightReportingSuffixQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
open scoped BigOperators
variable {lim : Limits}
namespace ThreeSum.LightReportingSuffixQuery
theorem _root_.solution {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset + V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W cut ≤ maskBase) (hdataR : baseR + (W + 1) * downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase + (V + 1) * downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase + LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work + 1 + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word) (ht : t ≤ Q.card + 1)
    (hboxCut : boxCut ≤ Q.card) (hflags : Q.card - t ≤ boxCut) (hdisjL : Disjoint preL (liftSet hfit Q))
    (hdisjR : Disjoint preR (liftSet hfit Q)) (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut) (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D) (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut (leafWeight hfit f g stage preL preR) V)
    (hd : d + W + 9 ≤ lim.depth) :
    Meets lim program 28 d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, V, 2 ^ offset, Q.card, subsetMask Q, t,
        baseL, baseR, boxCut, boxBase, maskBase, work]
      μ (time W V Q.card t)
      (fun r μ' =>
        r =
            Subset.mobius
              (fun S => SubsetStages.stageValue f stage (preL ∪ S) * SubsetStages.stageValue g stage (preR ∪ S))
              (liftSet hfit Q) ∧
          KeptBut μ μ' work maskBase (LightSparseQuery.queryItems Q.card t)) :=
  by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hboxV : boxCut ≤ V := hboxCut.trans hQcard
  have hoff : layerOffset Q.card t ≤ LightSparseQuery.queryItems Q.card t := by
    unfold LightSparseQuery.queryItems
    omega
  have hchoose : Q.card.choose t ≤ LightSparseQuery.queryItems Q.card t := by unfold LightSparseQuery.queryItems; omega
  have hproduct : (2 ^ stage * B) * (2 ^ stage * D) ≤ 2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos V)
  have hfullBound :
    2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D)) ≤ LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by unfold LightSparseQuery.queryItems; omega)
  have heBound :
    (layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) ≤
      LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul (Nat.succ_le_succ hoff) hproduct
  have hbBound :
    Q.card.choose t * (2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D))) ≤
      LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul_right _ (hchoose.trans (Nat.le_succ _))
  have hExplicitWord : (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast heBound :
          (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
            (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans
      hvalueWord
  have hBoxWord : ((Q.card.choose t * (2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D))) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbBound :
          ((Q.card.choose t * (2 ^ V * ((2 ^ stage * B) * (2 ^ stage * D))) : ℕ) : ℤ) ≤
            (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans
      hvalueWord
  have hCL : preL.card + Q.card ≤ cut := by simpa only [Finset.card_union_of_disjoint hdisjL, liftSet_card] using hcardL
  have hCR : preR.card + Q.card ≤ cut := by simpa only [Finset.card_union_of_disjoint hdisjR, liftSet_card] using hcardR
  have hweight (S : Finset (Fin V)) (hS : S.card ≤ Q.card) :
    |leafWeight hfit f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    apply leafWeight_abs_le (sourceCut := cut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans (by omega)
    · have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans (by omega)
    · exact hf
    · exact hg
  have htotal : |∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S| ≤ lim.word :=
    by
    have hs :
      |∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S| ≤
        ((2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
      by
      calc
        _ ≤ ∑ S ∈ Q.powerset, |leafWeight hfit f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Q.powerset, (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
          (Finset.sum_le_sum fun S hS => hweight S (Finset.card_le_card (Finset.mem_powerset.mp hS)))
        _ = _ := by simp [Nat.cast_mul]
    have hn : 2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) ≤ LightSparseQuery.magnitudeBound V stage Q.card t B D :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hQcard)).trans hfullBound
    have hz :
      ((2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
        (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) :=
      by exact_mod_cast hn
    exact hs.trans (hz.trans hvalueWord)
  apply Meets.of_body (p := 28) (by rfl : program[28]? = some (body 27 2 22))
  unfold body time
  have he :=
    LightReportingSuffixExplicit.meets (P := program) (pMain := 27) (d := d + 1) (μ := μ) (t := t) (baseL := baseL)
      (baseR := baseR) (maskBase := maskBase) (work := work) rfl explicitProcs hfit Q preL preR f g hw hcut hstage
      hdataL hdataR (by omega) hspace hword hExplicitWord ht hcardL hcardR hf hg hstoredL hstoredR (by omega)
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro explicit μ₁ ⟨heValue, hkeepE⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hstoredBox₁ :=
    ReportingHostQueryBounds.boxStored_of_on hstoredBox
      (by
        intro i _ hi
        have ha := hi.trans_le hdataBox
        exact hkeepE i ⟨by omega, Or.inl ha⟩)
  have hb :=
    LightCanonicalBoxSum.meets (P := program) (pMain := 2) (d := d + 1) (μ := μ₁) (t := t) (base := boxBase)
      (maskBase := maskBase) (work := work) rfl boxProcs Q (leafWeight hfit f g stage preL preR) hw hboxV hdataBox
      (by omega) (LightReportingSuffixCell.small_space hV hspace) (LightReportingSuffixCell.small_word hV hword)
      hBoxWord ht hflags (fun S hS => hweight S (hS.trans hboxCut)) hstoredBox₁ (by omega)
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
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro boxes μ₂ ⟨hbValue, hkeepB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hsum : explicit + boxes = ∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S :=
    by
    rw [heValue, hbValue]
    exact (ExplicitLayers.sparse_identity Q (leafWeight hfit f g stage preL preR) t).symm
  have htotalSides := abs_le.mp htotal
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsum] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hs := LightSign.meets (P := program) (pMain := 22) (d := d + 1) (μ := μ₂) (e := Q.card) rfl hw (by omega) htotal
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSign.time] <;> omega)
    on_goal -1 => (rintro res μ₃ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  refine ⟨hres.trans (query_eq_local_signed_sum hfit f g stage preL preR Q).symm, ?_⟩
  intro i hi
  exact
    (hkeepB i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩).trans (hkeepE i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩)
end ThreeSum.LightReportingSuffixQuery
