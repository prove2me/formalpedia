-- Prove2me | solution 1 for ThreeSum.LightReportingPairRows.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:56.580008+00:00
-- url     : https://prove2.me/submissions/e1f6fac1-1c38-423c-9635-113284deaeb5

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LayerCounts_vertex_degree_identity
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
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_7aba91d69ad782cd
import Definitions.Def_WeightedCache3SUM_Alias_4b224c9ee30c137c
import Definitions.Def_WeightedCache3SUM_Alias_dc0a334da481a327
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
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_mask
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rightAt_eq_get
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_subsetMask_univ_succ
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_card
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_empty
import Theorems.Thm_ThreeSum_ReportingHostSuffix_mem_lowerSet
import Theorems.Thm_ThreeSum_ReportingHostSuffix_shiftEmbedding_val
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPairRows
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration
set_option maxHeartbeats 1800000
variable {lim : Limits}
namespace ThreeSum.LightReportingPairRows
theorem _root_.solution {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2 * h ≤ L)
    (hS : srcS + L.choose h ≤ dstL) (hL : dstL + L.choose h * (L - h).choose h ≤ dstR)
    (hR : dstR + L.choose h * (L - h).choose h ≤ work) (hspace : work + 2 * L + 2 ≤ lim.space)
    (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + L + 3 ≤ lim.depth) :
    Meets lim program 7 d [L, h, srcS, dstL, dstR, work] μ (time L h)
      (fun r μ' =>
        r = (L.choose (2 * h) * (2 * h).choose h : ℤ) ∧
          SegN μ' srcS (enumerateLayer L h) ∧
            (∀ i < L.choose h,
                ∀ j < (L - h).choose h,
                  μ' (dstL + i * (L - h).choose h + j) = (subsetMask (leftAt L h i) : ℤ) ∧
                    μ' (dstR + i * (L - h).choose h + j) = (subsetMask (rightAt L h i j) : ℤ)) ∧
              Kept μ μ' srcS) :=
  by
  have hdeg : 0 < (L - h).choose h := Nat.choose_pos (by omega)
  have hverts : 0 < L.choose h := Nat.choose_pos (by omega)
  have hmask (S : Finset (Fin L)) : (subsetMask S : ℤ) ≤ lim.word :=
    by
    have hb : subsetMask S ≤ 2 ^ (L + 1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hb).trans hword
  have hfullWord := hmask (Finset.univ : Finset (Fin L))
  apply Meets.of_body (p := 7) (by rfl : program[7]? = some (body 5 0 6))
  unfold body time
  have hs :=
    LightSubsetEnumerationSetup.meets (P := program) (pMain := 5) (pPowers := 2) (pEnum := 4) (d := d + 1) (μ := μ)
      (L := L) (k := h) (dst := srcS) (work := work) rfl rfl rfl hw (by omega) hword (by omega) (by omega) (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetEnumerationSetup.time, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetEnumerationSetup.time, roundTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetEnumerationSetup.time, roundTime] <;> omega)
    on_goal -1 =>
      (rintro len μ₁ ⟨hlen, hlefts, hpowers, hkeepLayer⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst len
  have hpow := hpowers L le_rfl
  have hpowNat : μ₁ (work + L) = ((2 ^ L : ℕ) : ℤ) := by simpa using hpow
  have hfull : ((2 ^ L : ℕ) : ℤ) - 1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) :=
    by
    have he : (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) + 1 = ((2 ^ L : ℕ) : ℤ) := by
      exact_mod_cast subsetMask_univ_succ L
    omega
  have hfullInt : (2 : ℤ) ^ L - 1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by simpa using hfull
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (subsetMask (Finset.univ : Finset (Fin L)) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpow, hpowNat, hfull, hfullInt,
            LightSubsetEnumerationSetup.time, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hpow, hpowNat, hfull, hfullInt, LightSubsetEnumerationSetup.time, roundTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpow, hpowNat, hfull, hfullInt,
            LightSubsetEnumerationSetup.time, roundTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetEnumerationSetup.time, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetEnumerationSetup.time, roundTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetEnumerationSetup.time, roundTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (lim := lim) (P := program) (d := d) (i := 9) (hi := v 6) (body := roundBody 0 6) (T :=
        L.choose h * (roundTime L h + 20) + 70) (Q := Inv μ L h srcS dstL dstR work (L.choose h))
        (Inv μ L h srcS dstL dstR work) (L.choose h) (roundTime L h) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime] <;> first
              | omega
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, 0, 0, 0, μ₁, ?_, hlefts, ?_, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(L : ℤ), h, srcS, dstL, dstR, work, L.choose h, subsetMask (Finset.univ : Finset (Fin L)), 0, 0] =
          frame
            ([(L : ℤ), h, srcS, dstL, dstR, work, L.choose h, subsetMask (Finset.univ : Finset (Fin L)), 0, 0] ++
              [0, 0, 0, 0])
      exact (frame_append_zeros _ 4).symm
    · intro i hi; omega
    · intro i hi
      exact hkeepLayer i ⟨by omega, Or.inl hi⟩
  case round =>
    rintro j _ hj _ ⟨a, b, nr, r, μ', rfl, hlefts, hout, hkeep⟩
    have hjD : j * (L - h).choose h + (L - h).choose h ≤ L.choose h * (L - h).choose h :=
      by
      have hm := Nat.mul_le_mul_right ((L - h).choose h) (show j + 1 ≤ L.choose h by omega)
      nlinarith
    have hleftCard := leftAt_card hj
    have hcomp : (Finset.univ \ leftAt L h j).card = L - h := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hleftCard]
    have hread : μ' (srcS + j) = (subsetMask (leftAt L h j) : ℤ) :=
      by
      have hget := hlefts j (by simpa only [List.length_map, enumerateLayer_length] using hj)
      simpa only [List.getElem_map, leftAt_mask hj] using hget
    have hlword := hmask (leftAt L h j)
    have hcword := hmask (Finset.univ \ leftAt L h j)
    have hdiff := MaskDifference.subsetMask_sdiff_int Finset.univ (leftAt L h j) (Finset.subset_univ _)
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
      refine _root_.Light.Ends.setToThen (subsetMask (leftAt L h j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread, roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, roundTime] <;> omega)
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
      refine _root_.Light.Ends.setToThen (subsetMask (Finset.univ \ leftAt L h j) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdiff, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hdiff, roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdiff, roundTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hq :=
      LightQueryEnumeration.meets (P := program) (pMain := 0) (pWeights := 1) (pPowers := 2) (pErase := 3) (pEnum := 4)
        (d := d + 1) (μ := μ') (dst := dstR + j * (L - h).choose h) (work := work) (t := h) rfl rfl rfl rfl rfl
        (Finset.univ \ leftAt L h j) hw (by omega) hword (by rw [hcomp]; omega) (by rw [hcomp]; omega) (by omega)
    rw [hcomp] at hq
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
      | refine _root_.Light.Ends.callToThen (hq _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hq ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, roundTime] <;> omega)
      on_goal -1 =>
        (rintro count ν ⟨hcount, hnewR, hweights, hkeepQuery⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have ha :=
      LightReportingAffine.meets (P := program) (p := 6) (d := d + 1) (μ := ν) (src := dstR + j * (L - h).choose h)
        (dst := dstL + j * (L - h).choose h) (n := (L - h).choose h) (b := (subsetMask (leftAt L h j) : ℤ)) (c := 0) rfl
        hw (by omega) (by omega) (Or.inr (by omega)) (by intro i hi; simp only [zero_mul, abs_zero]; omega)
        (by intro i hi; simpa only [zero_mul, add_zero, Int.abs_natCast] using hlword)
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
      | refine _root_.Light.Ends.callToThen (ha _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen ha ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcount, roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, roundTime] <;> omega)
      on_goal -1 => (rintro affineRet ξ ⟨hnewL, hkeepAffine⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((j + 1) * (L - h).choose h : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, Nat.add_mul,
              roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcount, Nat.add_mul, roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, Nat.add_mul, roundTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, (subsetMask (leftAt L h j) : ℤ), (subsetMask (Finset.univ \ leftAt L h j) : ℤ), count, affineRet, ξ, ?_,
        ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      rw [hkeepAffine (srcS + i) (Or.inl (by simp only [List.length_map, enumerateLayer_length] at hi; omega)),
        hkeepQuery (srcS + i)
          ⟨by simp only [List.length_map, enumerateLayer_length] at hi; omega,
            Or.inl (by simp only [List.length_map, enumerateLayer_length] at hi; omega)⟩]
      exact hlefts i hi
    · intro i hi l hl
      by_cases he : i = j
      · subst i
        constructor
        · simpa only [zero_mul, add_zero, Nat.add_assoc] using hnewL l hl
        · rw [hkeepAffine _ (Or.inr (by omega))]
          have hlen : l < (rights (leftAt L h j) h).length := by rw [rights_length _ hleftCard]; exact hl
          have hr := hnewR l (by simpa only [List.length_map, rights] using hlen)
          simpa only [List.getElem_map, Nat.add_assoc, rights, rightAt_eq_get hj hl] using hr
      · have hij : i < j := by omega
        have hm := Nat.mul_le_mul_right ((L - h).choose h) (show i + 1 ≤ j by omega)
        obtain ⟨hprevL, hprevR⟩ := hout i hij l hl
        constructor
        · rw [hkeepAffine _ (Or.inl (by nlinarith)), hkeepQuery _ ⟨by nlinarith, Or.inl (by nlinarith)⟩]
          exact hprevL
        · rw [hkeepAffine _ (Or.inr (by omega)), hkeepQuery _ ⟨by nlinarith, Or.inl (by nlinarith)⟩]
          exact hprevR
    · intro i hi
      exact (hkeepAffine i (Or.inl (by omega))).trans ((hkeepQuery i ⟨by omega, Or.inl (by omega)⟩).trans (hkeep i hi))
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    rintro j _ hj _ ⟨a, b, nr, r, μ', rfl, _, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨a, b, nr, r, μ', rfl, hlefts, hout, hkeep⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (L.choose h * (L - h).choose h : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, roundTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨?_, hlefts, hout, hkeep⟩
    simp only [LayerCounts.vertex_degree_identity]
    rfl
end ThreeSum.LightReportingPairRows
