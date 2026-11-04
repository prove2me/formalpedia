-- Prove2me | solution 1 for ThreeSum.LightBandRawA.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:29.801429+00:00
-- url     : https://prove2.me/submissions/475dd358-52bf-42b8-b266-a084c5f83db8

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandCandidateRows_cells_length
import Theorems.Thm_ThreeSum_BandCandidateRows_count_bound
import Theorems.Thm_ThreeSum_BandCandidateRows_record_fields
import Theorems.Thm_ThreeSum_BandCandidateRows_seg_record
import Theorems.Thm_ThreeSum_BandRawA_Stored_append
import Theorems.Thm_ThreeSum_BandRawA_Stored_empty
import Definitions.Def_WeightedCache3SUM_Alias_ec90977bc5c0c435
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Theorems.Thm_ThreeSum_BandRawA_count_bound
import Theorems.Thm_ThreeSum_BandRawA_count_succ
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_succ
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
import Theorems.Thm_ThreeSum_BandRawA_row_position_lt
import Definitions.Def_WeightedCache3SUM_Alias_d977006578c6c630
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
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BandRawA.count_zero
attribute [local simp] ThreeSum.BandRawA.firstRows_zero
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
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}
namespace ThreeSum.LightBandRawA
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth)
    (hg : 0 < g) (hrecords : records + 4 * rs.length ≤ vals) (hsrc : src + n ≤ vals)
    (hspace : space vals rs.length g ≤ lim.space) (hword : (word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag = 1 → (rs.getD i default).a < BandPartition.size n g)
    (hrecordRead : Seg μ records (cells rs)) (hread : ∀ j < n, μ (src + j) = f j) :
    Meets lim P pMain d [records, rs.length, src, n, g, vals] μ (time rs.length g)
      (fun r ν =>
        r = ((items n g rs).length : ℤ) ∧
          Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g) f (items n g rs) ∧
            Kept μ ν vals) :=
  by
  have hspace' : vals + capacity rs.length g + capacity rs.length g + capacity rs.length g ≤ lim.space := hspace
  have hcapWord : (g : ℤ) * (rs.length : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show capacity rs.length g ≤ lim.space by omega) :
          (g : ℤ) * (rs.length : ℤ) ≤ (lim.space : ℤ)).trans
      hw
  have hcapNonneg : (0 : ℤ) ≤ (g : ℤ) * (rs.length : ℤ) := by positivity
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega : n ≤ word n g rs.length)).trans hword
  have hgWord : (g : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega : g ≤ word n g rs.length)).trans hword
  have hNWord : (rs.length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : rs.length ≤ word n g rs.length)).trans hword
  have howner : ownerBase vals rs.length g + capacity rs.length g = positionBase vals rs.length g := rfl
  have hvalues : vals + capacity rs.length g = ownerBase vals rs.length g := rfl
  have hposition : positionBase vals rs.length g + capacity rs.length g ≤ lim.space := hspace
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen (capacity rs.length g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, capacity]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [capacity] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, capacity] <;> omega)
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
    refine _root_.Light.Ends.setToThen (ownerBase vals rs.length g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ownerBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ownerBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ownerBase] <;> omega)
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
    refine _root_.Light.Ends.setToThen (positionBase vals rs.length g : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, positionBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [positionBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, positionBase] <;> omega)
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
      (Ends.for (T := rs.length * (LightBandRawAStep.time g + 200) + 6) (Q := Inv μ rs f records src n g vals rs.length)
        (Inv μ rs f records src n g vals) rs.length (LightBandRawAStep.time g + 192) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, 0, μ, ?_, Stored.empty _ _ _ _ _, SameOn.refl⟩
    simp only [count_zero]
    simp [update_frame_setLocal]
    exact
      (frame_append_zeros
          [records, rs.length, src, n, g, vals, capacity rs.length g, ownerBase vals rs.length g,
            positionBase vals rs.length g, 0, 0]
          2).symm
  case round =>
    rintro i _ hi _ ⟨flag, a, ν, rfl, stored, kept⟩
    have hnext : count n g rs (i + 1) ≤ capacity rs.length g :=
      by
      have hb := count_bound n g rs (i + 1)
      have hm := Nat.mul_le_mul_left g (show i + 1 ≤ rs.length by omega)
      exact hb.trans hm
    have hfit : count n g rs i + (BandRawA.row n g i (rs.getD i default)).length ≤ capacity rs.length g := by
      rwa [count_succ] at hnext
    have hstored : Seg ν records (cells rs) := hrecordRead.of_kept kept (by simpa only [cells_length] using hrecords)
    have hfields := record_fields (seg_record hstored hi)
    have hflag := hfields.1
    have hA := hfields.2.1
    have hstepWord : ((n + g + i + 10 : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by unfold word; omega : n + g + i + 10 ≤ word n g rs.length)).trans hword
    have hflagAddr : ((records : ℤ) + 4 * (i : ℤ)).toNat = records + 4 * i := by omega
    have hAAddr : ((records : ℤ) + 4 * (i : ℤ) + 1).toNat = records + 4 * i + 1 := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((rs.getD i default).flag : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagAddr, hflag]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hflagAddr, hflag] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagAddr, hflag] <;> omega)
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
      refine _root_.Light.Ends.setToThen ((rs.getD i default).a : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hAAddr, hA]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hAAddr, hA] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hAAddr, hA] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hc :=
      LightBandRawAStep.meets (d := d + 1) (μ := ν) (src := src) (n := n) (g := g) (owner := i) (r := rs.getD i default)
        (values := vals) (owners := ownerBase vals rs.length g) (positions := positionBase vals rs.length g)
        (previous := count n g rs i) (capacity := capacity rs.length g) S.step S.row S.copy S.fill hw (by omega) hg
        (hvalid i hi) hsrc hvalues.le howner.le hposition hfit hstepWord
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
      on_goal -1 => (rintro result ν₁ ⟨hresult, hout, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hresult' : result = (count n g rs (i + 1) : ℤ) := by simpa only [count_succ] using hresult
    have hold : Stored ν₁ vals (ownerBase vals rs.length g) (positionBase vals rs.length g) f (firstRows n g rs i) :=
      stored.keep_before_append hkeep hvalues.le howner.le hfit
    have hrowStored :
      Stored ν₁ (vals + count n g rs i) (ownerBase vals rs.length g + count n g rs i)
        (positionBase vals rs.length g + count n g rs i) f (BandRawA.row n g i (rs.getD i default)) :=
      by
      apply row_stored
      intro j hj
      have hp := row_position_lt hj
      refine ⟨?_, (hout j hj).2.1, (hout j hj).2.2⟩
      rw [(hout j hj).1, kept _ (by omega)]
      simpa only [Nat.add_assoc] using hread _ hp
    refine ⟨by simp, (rs.getD i default).flag, (rs.getD i default).a, ν₁, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal, hresult']
    · rw [firstRows_succ]
      exact hold.append hrowStored
    · intro addr ha
      rw [hkeep addr ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩, kept addr ha]
  case done =>
    rintro _ _ ⟨flag, a, ν, rfl, stored, kept⟩
    exact ⟨flag, a, ν, rfl, stored, kept⟩
  case bound =>
    rintro i _ _ _ ⟨flag, a, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨flag, a, ν, rfl, stored, kept⟩
    have hc := count_bound n g rs rs.length
    have hcWord : (count n g rs rs.length : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr
            (show count n g rs rs.length ≤ lim.space
              by
              change count n g rs rs.length ≤ capacity rs.length g at hc
              omega)).trans
        hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (count n g rs rs.length : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, stored, kept⟩
end Procs
end ThreeSum.LightBandRawA
