-- Prove2me | solution 1 for ThreeSum.LightWantedJoin.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:53.955346+00:00
-- url     : https://prove2.me/submissions/246363ed-71f7-4453-bb56-d082c946afa4

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
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
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightHistogram_count_succ
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_read_bucket
import Theorems.Thm_ThreeSum_SourceBuckets_count_mono
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le
import Theorems.Thm_ThreeSum_SourceBuckets_offset_succ
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WantedPairs_cells_append
import Theorems.Thm_ThreeSum_WantedPairs_cells_length
import Theorems.Thm_ThreeSum_WantedPairs_count_mono
import Theorems.Thm_ThreeSum_WantedPairs_count_succ
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_length
import Theorems.Thm_ThreeSum_WantedPairs_pairs_succ
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Definitions.Def_WeightedCache3SUM_Alias_4080c44d3b82d55b
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
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
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWantedJoin
theorem _root_.solution {pMain pRow keys offsets flat NR M dst : ℕ} (hmain : P[pMain]? = some (body pMain pRow))
    (hrow : P[pRow]? = some LightWantedRow.body) (left right : ℕ → ℕ) (hright : ∀ j < NR, right j < M) :
    ∀ n d : ℕ,
      ∀ μ : ℕ → ℤ,
        (lim.space : ℤ) ≤ lim.word →
          keys + n ≤ dst →
            offsets + M + 1 ≤ dst →
              flat + NR ≤ dst →
                dst + 2 * count left right NR n ≤ lim.space →
                  d + n + 2 ≤ lim.depth →
                    (∀ i < n, left i < M) →
                      (∀ i < n, μ (keys + i) = (left i : ℤ)) →
                        Stored μ right NR M offsets flat →
                          Meets lim P pMain d [keys, offsets, flat, n, NR, M, dst] μ (time left right NR n)
                            (fun r ν =>
                              r = (count left right NR n : ℤ) ∧
                                Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) :=
  by
  intro n
  induction n with
  | zero =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
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
    exact ⟨rfl, by simp [cells], fun _ _ => rfl⟩
  | succ n ih =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    let previous := count left right NR n
    let size := LightHistogram.count right (left n) NR
    let start := offset right NR (left n)
    have htotal : count left right NR (n + 1) = previous + size := count_succ left right NR n
    have hspace' : dst + 2 * (previous + size) ≤ lim.space := by rwa [htotal] at hspace
    have hcode := hleft n (by omega)
    have hstart : start ≤ NR := offset_le hright (by omega)
    have hend : start + size ≤ NR :=
      by
      have hh := offset_le hright (show left n + 1 ≤ M by omega)
      rw [offset_succ] at hh
      exact hh
    have hprevious : previous ≤ count left right NR (n + 1) := count_mono left right NR (by omega)
    have hpreviousWord : (previous : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show previous ≤ lim.space by omega)).trans hw
    have hsizeWord : (size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show size ≤ lim.space by omega)).trans hw
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    have hprev :=
      ih (d + 1) μ hw (by omega) hoffsets hflat (by omega) (by omega) (fun i hi => hleft i (by omega))
        (fun i hi => hread i (by omega)) H
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
      | refine _root_.Light.Ends.callToThen (hprev _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hprev ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedRow.time] <;> omega)
      on_goal -1 => (rintro prev μ₁ ⟨hprev, hstored, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hreadCode : μ₁ (keys + n) = (left n : ℤ) := (hkeep₁ _ (by omega)).trans (hread n (by omega))
    have hreadCodeZ : μ₁ (((keys : ℤ) + (n : ℤ)).toNat) = (left n : ℤ) :=
      by
      rw [show ((keys : ℤ) + (n : ℤ)).toNat = keys + n by omega]
      exact hreadCode
    have hreadStart : μ₁ (offsets + left n) = (start : ℤ) := (hkeep₁ _ (by omega)).trans (H.offsets (left n) (by omega))
    have hreadStartZ : μ₁ (((offsets : ℤ) + (left n : ℤ)).toNat) = (start : ℤ) :=
      by
      rw [show ((offsets : ℤ) + (left n : ℤ)).toNat = offsets + left n by omega]
      exact hreadStart
    have hreadStop : μ₁ (offsets + left n + 1) = ((start + size : ℕ) : ℤ) := by
      rw [hkeep₁ _ (by omega), Nat.add_assoc, H.offsets (left n + 1) (by omega), offset_succ]
    have hreadStopZ : μ₁ (((offsets : ℤ) + (left n : ℤ) + 1).toNat) = ((start + size : ℕ) : ℤ) :=
      by
      rw [show ((offsets : ℤ) + (left n : ℤ) + 1).toNat = offsets + left n + 1 by omega]
      exact hreadStop
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWantedRow.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (left n : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadCodeZ,
              LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadCodeZ, LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadCodeZ, LightWantedRow.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (start : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadStartZ,
              LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadStartZ, LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadStartZ, LightWantedRow.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (size : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadStopZ,
              LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadStopZ, LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadStopZ, LightWantedRow.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hflatRead (t : ℕ) (ht : t < size) : μ₁ (flat + start + t) = μ (flat + start + t) := hkeep₁ _ (by omega)
    have hrowValues (t : ℕ) (ht : t < size) : |μ₁ (flat + start + t)| ≤ lim.word :=
      by
      obtain ⟨j, hj, _, _, hjRead⟩ := H.read_bucket hright hcode ht
      rw [hflatRead t ht, hjRead, Int.abs_natCast]
      exact (Int.ofNat_le.mpr (show j ≤ lim.space by omega)).trans hw
    have hc :=
      LightWantedRow.meets (d := d + 1) (μ := μ₁) (left := n) (src := flat) (start := start) (n := size) (dst := dst)
        (previous := previous) hrow hw (by omega) hspace' ((Int.ofNat_le.mpr (show n ≤ lim.space by omega)).trans hw)
        hrowValues
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hprev, previous,
              size, LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hprev, previous, size, LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hprev, previous, size,
              LightWantedRow.time] <;> omega)
      on_goal -1 => (rintro unused μ₂ ⟨hout, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnew : Seg μ₂ (dst + 2 * previous) (cells (row μ offsets flat left n)) :=
      by
      apply row_segment H hright hcode
      intro t ht
      exact ⟨(hout t ht).1, (hout t ht).2.trans (hflatRead t ht)⟩
    have holdLen : (cells (pairs μ offsets flat left n)).length = 2 * previous := by
      rw [cells_length, pairs_length H n (fun i hi => hleft i (by omega))]
    have hold : Seg μ₂ dst (cells (pairs μ offsets flat left n)) :=
      hstored.of_sameOutside hkeep₂ (Or.inl (by rw [holdLen]))
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (count left right NR (n + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, htotal, hprev,
              previous, size, LightWantedRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [htotal, hprev, previous, size, LightWantedRow.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htotal, hprev, previous, size,
              LightWantedRow.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨rfl, ?_, ?_⟩
    · rw [pairs_succ, cells_append]
      apply seg_append.mpr
      exact ⟨hold, by simpa only [holdLen] using hnew⟩
    · intro a ha
      change μ₂ a = μ a
      exact (hkeep₂ a (Or.inl (by omega))).trans (hkeep₁ a ha)
end ThreeSum.LightWantedJoin
