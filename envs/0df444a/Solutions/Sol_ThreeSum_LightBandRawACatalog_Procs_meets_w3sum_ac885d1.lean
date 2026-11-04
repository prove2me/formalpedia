-- Prove2me | solution 1 for ThreeSum.LightBandRawACatalog.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:37:11.30298+00:00
-- url     : https://prove2.me/submissions/4f28c3a1-b658-49ed-825b-0d6ebdb1aff5

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BandCandidateRows_cells_length
import Theorems.Thm_ThreeSum_BandCandidateRows_records_length
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Theorems.Thm_ThreeSum_BandRawA_count_zero
import Theorems.Thm_ThreeSum_BandRawA_firstRows_zero
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
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Theorems.Thm_ThreeSum_LightBandRawA_Procs_meets_candidates
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
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
open ThreeSum ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {tables rec src headerA headerB headerC nA nB nC g vals : ℕ}
  {f : ℕ → ℤ}
namespace ThreeSum.LightBandRawACatalog
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) (A B C : Family) (hA : A.size = BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hg : 0 < g)
    (htable : tables + LightBandEnumeration.count A.size B.size C.size ≤ rec) (hsrc : src + nA ≤ rec)
    (hheadA : headerA + 2 ≤ rec) (hheadB : headerB + 2 ≤ rec) (hheadC : headerC + 2 ≤ rec)
    (hrec : rec + 4 * LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : space vals A.size B.size C.size g ≤ lim.space) (hword : (word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : LightHeaderBands.At μ headerA nA A) (hheaderB : LightHeaderBands.At μ headerB nB B)
    (hheaderC : LightHeaderBands.At μ headerC nC C) (htables : LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src + j) = f j) :
    Meets lim P pMain d [tables, rec, src, headerA, headerB, headerC, g, vals] μ (time A.size B.size C.size g)
      (fun r ν =>
        r = ((items nA g (records A B C)).length : ℤ) ∧
          Seg ν rec (cells (records A B C)) ∧
            Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
                (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g) f
                (items nA g (records A B C)) ∧
              Kept μ ν rec) :=
  by
  have hvals : vals ≤ lim.space :=
    by
    unfold space LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase at hspace
    omega
  have hcandidateSpace : LightBandCandidates.space rec A.size B.size C.size ≤ lim.space :=
    by
    unfold LightBandCandidates.space
    omega
  have hcandidateWord : (LightBandCandidates.word A.size B.size C.size : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (by unfold word; omega :
            LightBandCandidates.word A.size B.size C.size ≤ word nA A.size B.size C.size g)).trans
      hword
  have hrawWord : (LightBandRawA.word nA g (LightBandEnumeration.count A.size B.size C.size) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (by unfold word; omega :
            LightBandRawA.word nA g (LightBandEnumeration.count A.size B.size C.size) ≤
              word nA A.size B.size C.size g)).trans
      hword
  have h1Word : (1 : ℤ) ≤ lim.word :=
    by
    have hh : 1 ≤ word nA A.size B.size C.size g := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnRead := hheaderA.1
  have haRead := hheaderA.2.1
  have hbRead := hheaderB.2.1
  have hcRead := hheaderC.2.1
  have haAddr : ((headerA : ℤ) + 1).toNat = headerA + 1 := by omega
  have hbAddr : ((headerB : ℤ) + 1).toNat = headerB + 1 := by omega
  have hcAddr : ((headerC : ℤ) + 1).toNat = headerC + 1 := by omega
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
    refine _root_.Light.Ends.setToThen (nA : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hnRead]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hnRead] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hnRead] <;> omega)
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
    refine _root_.Light.Ends.setToThen (A.size : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haAddr, haRead]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [haAddr, haRead] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haAddr, haRead] <;> omega)
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
    refine _root_.Light.Ends.setToThen (B.size : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbAddr, hbRead]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbAddr, hbRead] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbAddr, hbRead] <;> omega)
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
    refine _root_.Light.Ends.setToThen (C.size : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcAddr, hcRead]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcAddr, hcRead] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcAddr, hcRead] <;> omega)
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((S.candidates.meets (d := d + 1) A B C hw (by omega) htable hcandidateSpace hcandidateWord htables) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (S.candidates.meets (d := d + 1) A B C hw (by omega) htable hcandidateSpace hcandidateWord htables) ?_ ?_ ?_
          ?_
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
    on_goal -1 =>
      (rintro countResult ν₁ ⟨hcount, hrecords, hkeepCandidates⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hsource : ∀ j < nA, ν₁ (src + j) = f j := by
    intro j hj
    rw [hkeepCandidates _ (Or.inl (by omega))]
    exact hread j hj
  have hraw :=
    S.raw.meets_candidates (d := d + 1) (records := rec) (src := src) (vals := vals) (n := nA) (g := g) (f := f) A B C
      hA hw (by omega) hg (by simpa only [records_length] using hrec) (by omega)
      (by simpa only [records_length, space] using hspace) (by simpa only [records_length] using hrawWord) hrecords
      hsource
  have hraw' :
    Meets lim P S.pRaw (d + 1) [rec, LightBandEnumeration.count A.size B.size C.size, src, nA, g, vals] ν₁
      (LightBandRawA.time (LightBandEnumeration.count A.size B.size C.size) g)
      (fun r ν =>
        r = ((items nA g (records A B C)).length : ℤ) ∧
          Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
              (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g) f
              (items nA g (records A B C)) ∧
            Kept ν₁ ν vals) :=
    by simpa only [records_length] using hraw
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
    | refine _root_.Light.Ends.callToThen (hraw' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hraw' ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega)
    on_goal -1 =>
      (rintro result ν₂ ⟨hresult, hstored, hkeepRaw⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hresult, ?_, hstored, ?_⟩
  · exact hrecords.of_kept hkeepRaw (by simpa only [cells_length, records_length] using hrec)
  · intro addr ha
    change ν₂ addr = μ addr
    rw [hkeepRaw addr (by omega), hkeepCandidates addr (Or.inl ha)]
end Procs
end ThreeSum.LightBandRawACatalog
