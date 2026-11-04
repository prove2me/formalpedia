-- Prove2me | solution 1 for ThreeSum.LightBandCandidates.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:52.519224+00:00
-- url     : https://prove2.me/submissions/9b4639b8-7e92-43d1-88af-774f75f2ff76

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates
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
import Theorems.Thm_ThreeSum_BandCandidateRows_cells_length
import Theorems.Thm_ThreeSum_BandCandidateRows_index_lt
import Theorems.Thm_ThreeSum_BandCandidateRows_rect_length
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
import Theorems.Thm_ThreeSum_LightBandCandidatesTable_meets_segment
import Theorems.Thm_ThreeSum_LightBandLookup_result_le
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
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
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst : ℕ}
namespace ThreeSum.LightBandCandidates
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 < lim.depth) (hsrc : src + LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space) (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim P pMain d [src, dst, A.size, B.size, C.size] μ (time A.size B.size C.size)
      (fun r ν =>
        r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
          Seg ν dst (cells (records A B C)) ∧
            SameOutside μ ν dst (4 * LightBandEnumeration.count A.size B.size C.size)) :=
  by
  let U := A.size + B.size + C.size
  let bcN := B.size * C.size
  let abN := A.size * B.size
  let acN := A.size * C.size
  have hcount : LightBandEnumeration.count A.size B.size C.size = bcN + abN + acN := rfl
  have hsrc' : src + bcN + abN + acN ≤ dst := by simpa only [hcount, Nat.add_assoc] using hsrc
  have hspace' : dst + 4 * (bcN + abN + acN) ≤ lim.space := hspace
  have hAU : A.size ≤ U := by unfold U; omega
  have hBU : B.size ≤ U := by unfold U; omega
  have hCU : C.size ≤ U := by unfold U; omega
  have hwordU : ((U + 10 : ℕ) : ℤ) ≤ lim.word := hword
  have hAWord : (A.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : A.size ≤ U + 10)).trans hwordU
  have hBWord : (B.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : B.size ≤ U + 10)).trans hwordU
  have hCWord : (C.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : C.size ≤ U + 10)).trans hwordU
  have hbcWord : (B.size : ℤ) * (C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show bcN ≤ lim.space by omega) : (B.size : ℤ) * (C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ) * (B.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show abN ≤ lim.space by omega) : (A.size : ℤ) * (B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ) * (C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show acN ≤ lim.space by omega) : (A.size : ℤ) * (C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ) * (C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ) * (B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ) * (C.size : ℤ) := by positivity
  have hbcBound :
    ∀ j < B.size, ∀ k < C.size, LightBandLookup.result A.lower A.upper A.size (C.lower k - B.upper j) ≤ U :=
    by
    intro j _ k _
    exact (LightBandLookup.result_le _ _ _ _ A.sorted).trans hAU
  have habBound :
    ∀ i < A.size, ∀ j < B.size, LightBandLookup.result C.lower C.upper C.size (A.lower i + B.lower j) ≤ U :=
    by
    intro i _ j _
    exact (LightBandLookup.result_le _ _ _ _ C.sorted).trans hCU
  have hacBound :
    ∀ i < A.size, ∀ k < C.size, LightBandLookup.result B.lower B.upper B.size (C.lower k - A.lower i) ≤ U :=
    by
    intro i _ k _
    exact (LightBandLookup.result_le _ _ _ _ B.sorted).trans hBU
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
    refine _root_.Light.Ends.setToThen (bcN : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bcN]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [bcN] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bcN] <;> omega)
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
    refine _root_.Light.Ends.setToThen (abN : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, abN]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [abN] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, abN] <;> omega)
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
    refine _root_.Light.Ends.setToThen (acN : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, acN]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [acN] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, acN] <;> omega)
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
    refine _root_.Light.Ends.setToThen (bcN + abN + acN : ℕ) ?_ ?_ ?_
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
  have hcBC :=
    LightBandCandidatesTable.meets_segment (d := d + 1) (μ := μ) (src := src) (dst := dst) .bc S.bc S.rowBC S.cellBC hw
      (by omega) (by change src + bcN ≤ dst; omega) (by change dst + 4 * bcN ≤ lim.space; omega) hwordU hBU hCU hbcBound
      htables.1
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
    | refine _root_.Light.Ends.callToThen (hcBC _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcBC ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandCandidatesTable.time, LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> omega)
    on_goal -1 => (rintro unused ν₁ ⟨hbc, hkeepBC⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have habRead :
    ∀ i < A.size,
      ∀ j < B.size,
        ν₁ (src + bcN + i * B.size + j) = (LightBandLookup.result C.lower C.upper C.size (A.lower i + B.lower j) : ℤ) :=
    by
    intro i hi j hj
    have hh := index_lt hi hj
    rw [hkeepBC _ (Or.inl (by change i * B.size + j < abN at hh; omega))]
    exact htables.2.1 i hi j hj
  have hcAB :=
    LightBandCandidatesTable.meets_segment (d := d + 1) (μ := ν₁) (src := src + bcN) (dst := dst + 4 * bcN) .ab S.ab
      S.rowAB S.cellAB hw (by omega) (by change src + bcN + abN ≤ dst + 4 * bcN; omega)
      (by change dst + 4 * bcN + 4 * abN ≤ lim.space; omega) hwordU hAU hBU habBound habRead
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
    | refine _root_.Light.Ends.callToThen (hcAB _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcAB ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandCandidatesTable.time, LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> omega)
    on_goal -1 => (rintro unused ν₂ ⟨hab, hkeepAB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hacRead :
    ∀ i < A.size,
      ∀ k < C.size,
        ν₂ (src + bcN + abN + i * C.size + k) =
          (LightBandLookup.result B.lower B.upper B.size (C.lower k - A.lower i) : ℤ) :=
    by
    intro i hi k hk
    have hh := index_lt hi hk
    rw [hkeepAB _ (Or.inl (by change i * C.size + k < acN at hh; omega)),
      hkeepBC _ (Or.inl (by change i * C.size + k < acN at hh; omega))]
    exact htables.2.2 i hi k hk
  have hcAC :=
    LightBandCandidatesTable.meets_segment (d := d + 1) (μ := ν₂) (src := src + bcN + abN) (dst :=
      dst + 4 * (bcN + abN)) .ac S.ac S.rowAC S.cellAC hw (by omega)
      (by change src + bcN + abN + acN ≤ dst + 4 * (bcN + abN); omega)
      (by change dst + 4 * (bcN + abN) + 4 * acN ≤ lim.space; omega) hwordU hAU hCU hacBound hacRead
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
    | refine _root_.Light.Ends.callToThen (hcAC _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcAC ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandCandidatesTable.time, LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandCandidatesTable.time,
            LightBandCandidatesRow.time, LightBandCandidatesCell.time] <;> omega)
    on_goal -1 => (rintro unused ν₃ ⟨hac, hkeepAC⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hbc' : Seg ν₃ dst (cells (rect B.size C.size (BandCandidateRows.bc A B C))) := by
    apply
      (hbc.of_sameOutside hkeepAB (Or.inl (by rw [cells_length, rect_length]))).of_sameOutside hkeepAC
        (Or.inl (by rw [cells_length, rect_length]; change dst + 4 * bcN ≤ dst + 4 * (bcN + abN); omega))
  have hab' : Seg ν₃ (dst + 4 * bcN) (cells (rect A.size B.size (BandCandidateRows.ab A B C))) :=
    hab.of_sameOutside hkeepAC
      (Or.inl
        (by
          rw [cells_length, rect_length]
          change dst + 4 * bcN + 4 * abN ≤ dst + 4 * (bcN + abN)
          omega))
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (LightBandEnumeration.count A.size B.size C.size : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcount] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · rw [records, cells, List.flatMap_append, List.flatMap_append]
    change
      Seg ν₃ dst
        (cells (rect B.size C.size (BandCandidateRows.bc A B C)) ++
          (cells (rect A.size B.size (BandCandidateRows.ab A B C)) ++
            cells (rect A.size C.size (BandCandidateRows.ac A B C))))
    apply seg_append.mpr
    refine ⟨hbc', ?_⟩
    rw [cells_length, rect_length]
    apply seg_append.mpr
    refine ⟨hab', ?_⟩
    rw [cells_length, rect_length]
    change
      Seg ν₃ (dst + 4 * bcN + 4 * abN)
        (cells
          (rect A.size C.size
            (fun i k => make .ac i k (LightBandLookup.result B.lower B.upper B.size (C.lower k - A.lower i)))))
    rw [show dst + 4 * bcN + 4 * abN = dst + 4 * (bcN + abN) by ring]
    exact hac
  · intro a ha
    change ν₃ a = μ a
    unfold Outside at ha
    rw [hkeepAC a (by unfold Outside; rw [hcount] at ha; omega),
      hkeepAB a (by unfold Outside; rw [hcount] at ha; omega), hkeepBC a (by unfold Outside; rw [hcount] at ha; omega)]
end Procs
end ThreeSum.LightBandCandidates
