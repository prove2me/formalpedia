-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedBatch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:12.50614+00:00
-- url     : https://prove2.me/submissions/9d3bf222-71dc-4896-95e3-2b02aa7d7dea

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Theorems.Thm_ThreeSum_LightTernaryWantedBatch_rows_length_le
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
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
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_program_from_zero
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
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
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBatch
open Light LightTernaryWantedCanonical
open TernaryWantedLittleEndian (wantedCodes)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits}
namespace ThreeSum.LightTernaryWantedBatch
theorem _root_.solution {P R S C V work J d targetBase positionBase n dst : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ)) (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S) (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2 * V) work) (μ : ℕ → ℤ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (htarget : targetBase + n ≤ dst) (hpositions : positionBase + n ≤ dst)
    (htRead : ∀ i < n, μ (targetBase + i) = targets i) (hpRead : ∀ i < n, μ (positionBase + i) = (positions i : ℤ))
    (htBound : ∀ i < n, |targets i| ≤ (V : ℤ)) (hc : (((2 * R) ^ J : ℕ) : ℤ) ≤ lim.word)
    (hm : (((2 * S) ^ J : ℕ) : ℤ) ≤ lim.word) (ho : ∀ i < n, (positions i : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word)
    (hs : dst + 3 * n * C ^ J ≤ work) (hd : d + J + 4 ≤ lim.depth) :
    Meets lim (program P R S raws words maps) 4 d [J, targetBase, positionBase, n, dst, work] μ (time P C V J n)
      (fun r ν =>
        r = ((dst + (rows P R S J raws words maps targets positions n).length : ℕ) : ℤ) ∧
          Seg ν dst (rows P R S J raws words maps targets positions n) ∧ Kept μ ν dst) :=
  by
  have hw := F.space
  have hwork := F.free
  apply Meets.of_body (by rfl)
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
    refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := n * ((overhead P V + stepCost V + 40) * (J + 1) * C ^ J + 100) + 10) (Q :=
        Inv μ P R S J targetBase positionBase n dst work raws words maps targets positions n)
        (Inv μ P R S J targetBase positionBase n dst work raws words maps targets positions) n
        ((overhead P V + stepCost V + 40) * (J + 1) * C ^ J + 90) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨μ, ?_, ?_, SameOn.refl⟩
    · simp [rows, update_frame_setLocal]
    · simp [rows, Seg]
  case round =>
    rintro i _ hi _ ⟨ν, rfl, written, kept⟩
    let outPrefix := rows P R S J raws words maps targets positions i
    have hlen := rows_length_le P R S J C raws words maps targets positions hcap i
    have hinc : 3 * (i + 1) * C ^ J ≤ 3 * n * C ^ J :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (by omega : i + 1 ≤ n))
    have hcursor : dst + outPrefix.length + 3 * C ^ J ≤ work := by dsimp [outPrefix]; nlinarith
    have hcursorWord : ((dst + (rows P R S J raws words maps targets positions i).length : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : dst + (rows P R S J raws words maps targets positions i).length ≤ lim.space :=
        by
        change dst + outPrefix.length ≤ lim.space
        omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have htr : ν (targetBase + i) = targets i := (kept _ (by omega)).trans (htRead i hi)
    have hpr : ν (positionBase + i) = (positions i : ℤ) := (kept _ (by omega)).trans (hpRead i hi)
    have htargetaddr : ((targetBase : ℤ) + (i : ℤ)).toNat = targetBase + i := by omega
    have hpositionaddr : ((positionBase : ℤ) + (i : ℤ)).toNat = positionBase + i := by omega
    have hcall :=
      (LightTernaryWantedCanonical.program_from_zero (d := d + 1) hp hN hR hS hC hcap hraw hwords hmaps hRW hSW hNW F
            (targets i) (positions i) (dst + outPrefix.length) ν (htBound i hi) hc hm (ho i hi) hJ hcursor
            (by omega)).append
        [body]
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, htr, hpr,
              htargetaddr, hpositionaddr, frame, outPrefix]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [htr, hpr, htargetaddr, hpositionaddr, frame, outPrefix] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htr, hpr, htargetaddr, hpositionaddr, frame,
              outPrefix] <;> omega)
      on_goal -1 => (rintro r ξ ⟨hr, hrBound, hseg, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, ξ, ?_, ?_, ?_⟩
    · simp [rows, outPrefix, List.length_append, hr, update_frame_setLocal, add_assoc]
    · rw [rows]
      apply (seg_append).mpr
      refine ⟨?_, hseg⟩
      intro k hk
      rw [hkeep _ (by dsimp [outPrefix]; omega)]
      exact written k hk
    · intro k hk
      exact (hkeep _ (by omega)).trans (kept _ hk)
  case done => rintro _ _ h; exact h
  case bound =>
    rintro i _ _ _ ⟨ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨ν, rfl, written, kept⟩
    have hlen := rows_length_le P R S J C raws words maps targets positions hcap n
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (dst + (rows P R S J raws words maps targets positions n).length : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, written, kept⟩
end ThreeSum.LightTernaryWantedBatch
