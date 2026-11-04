-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedCanonical.recordSteps_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:52.895887+00:00
-- url     : https://prove2.me/submissions/a4ae94b4-15df-4ea5-a05c-dd355f1200b8

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
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
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
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
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
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
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_child_target_bound
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedRadix_localBucket_eq_of_emod
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le
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
open ThreeSum ThreeSum.LightTernaryWantedCanonical
open Light
open TernaryWantedRadix (localBucket mem_localBucket localBucket_eq_of_emod wantedOutputs wantedOutputs_length_le
  child_target_bound codeLimit codeLimit_base codeLimit_child)
open TernaryWantedLittleEndian (wantedCodes wantedCodes_length wantedCodes_succ encode)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {Prog : Program} {d : ℕ}
namespace ThreeSum.LightTernaryWantedCanonical
theorem _root_.solution {pMain pDivide pDecode P R S C V j : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body) (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R)
    (hS : 1 ≤ S) (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ)) (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S) (x : ℤ) (code scale mapCode mapScale original baseDst work : ℕ)
    (F : Emod.Pre lim P (2 * V) work) (hx : |x| ≤ (V : ℤ)) (hc : (codeLimit R code scale (j + 1) : ℤ) ≤ lim.word)
    (hm : (codeLimit S mapCode mapScale (j + 1) : ℤ) ≤ lim.word) (ho : (original : ℤ) ≤ lim.word)
    (hJ : ((j + 1 : ℕ) : ℤ) ≤ lim.word) (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (hd : d + j + 3 ≤ lim.depth)
    (hchild :
      ∀ (i : ℕ),
        i ∈ localBucket (P : ℤ) raws x →
          ∀ (dst : ℕ) (ν : ℕ → ℤ),
            dst + 3 * C ^ j ≤ work →
              Meets lim Prog pMain (d + 1)
                [j, (x - raws.getD i 0) / (P : ℤ), code + scale * words.getD i 0, scale * R,
                  mapCode + mapScale * maps.getD i 0, mapScale * S, original, dst, work]
                ν (time P C V j)
                (fun r ξ =>
                  r =
                      ((dst +
                            3 *
                              (wantedCodes (P : ℤ) raws words maps j ((x - raws.getD i 0) / (P : ℤ)) R S
                                  (code + scale * words.getD i 0) (scale * R) (mapCode + mapScale * maps.getD i 0)
                                  (mapScale * S)).length :
                          ℕ) :
                        ℤ) ∧
                    Seg ξ dst
                        (rowCells original
                          (wantedCodes (P : ℤ) raws words maps j ((x - raws.getD i 0) / (P : ℤ)) R S
                            (code + scale * words.getD i 0) (scale * R) (mapCode + mapScale * maps.getD i 0)
                            (mapScale * S))) ∧
                      Kept ν ξ dst)) :
    ∀ (is : List ℕ),
      (∀ i ∈ is, i ∈ localBucket (P : ℤ) raws x) →
        ∀ (cursor : ℕ) (q residue : ℤ) (μ : ℕ → ℤ),
          cursor + 3 * is.length * C ^ j ≤ work →
            Ends lim Prog d (recordSteps pMain pDivide P R S raws words maps is)
              ⟨frame [j + 1, x, code, scale, mapCode, mapScale, original, baseDst, work, q, cursor, residue], μ⟩
              (is.length * (stepCost V + time P C V j))
              (fun σ =>
                ∃ q',
                  σ.loc =
                      frame
                        [j + 1, x, code, scale, mapCode, mapScale, original, baseDst, work, q',
                          cursor + 3 * (branchCodes P R S raws words maps j x code scale mapCode mapScale is).length,
                          residue] ∧
                    Seg σ.mem cursor
                        (rowCells original (branchCodes P R S raws words maps j x code scale mapCode mapScale is)) ∧
                      Kept μ σ.mem cursor) :=
  by
  intro is
  induction is with
  | nil =>
    intro hi cursor q residue μ hs
    exact
      Ends.skip
        ⟨q, by simp [branchCodes], by simp [branchCodes, rowCells, TernaryWantedCanonicalPairs.rowCells], fun _ _ =>
          rfl⟩
  | cons i is ih =>
    intro hall cursor q residue μ hs
    obtain ⟨hi, hdiv⟩ := (mem_localBucket _ _ _ _).mp (hall i (by simp))
    have hbase := codeLimit_base (code := code) (scale := scale) (j := j + 1) hR
    have hcode : (code : ℤ) ≤ lim.word := by omega
    have hscale : (scale : ℤ) ≤ lim.word := by omega
    have hmapbase := codeLimit_base (code := mapCode) (scale := mapScale) (j := j + 1) hS
    have hmapCodeW : (mapCode : ℤ) ≤ lim.word := by omega
    have hmapScaleW : (mapScale : ℤ) ≤ lim.word := by omega
    have hchildlim := codeLimit_child (code := code) (scale := scale) (j := j) hR (hwords i hi)
    have hb := codeLimit_base (code := code + scale * words.getD i 0) (scale := scale * R) (j := j) hR
    have hmchild := codeLimit_child (code := mapCode) (scale := mapScale) (j := j) hS (hmaps i hi)
    have hmb := codeLimit_base (code := mapCode + mapScale * maps.getD i 0) (scale := mapScale * S) (j := j) hS
    have hcCode : ((code + scale * words.getD i 0 : ℕ) : ℤ) ≤ lim.word := by omega
    have hcScale : ((scale * R : ℕ) : ℤ) ≤ lim.word := by omega
    have hmCode : ((mapCode + mapScale * maps.getD i 0 : ℕ) : ℤ) ≤ lim.word := by omega
    have hmScale : ((mapScale * S : ℕ) : ℤ) ≤ lim.word := by omega
    have hwordDigit : ((words.getD i 0) : ℤ) ≤ lim.word := by have hh := hwords i hi; omega
    have hmapDigit : ((maps.getD i 0) : ℤ) ≤ lim.word := by have hh := hmaps i hi; omega
    have hiW : (i : ℤ) ≤ lim.word := by omega
    have hcursor : (cursor : ℤ) ≤ lim.word := by
      have hf := F.free
      have hw := F.space
      omega
    have htarget := hraw i hi
    have hdiff : |x - raws.getD i 0| ≤ ((2 * V : ℕ) : ℤ) :=
      by
      have hh : |x - raws.getD i 0| ≤ |x| + |raws.getD i 0| := by simpa using abs_sub_le x 0 (raws.getD i 0)
      push_cast
      linarith
    have ha : (x - raws.getD i 0).natAbs ≤ 2 * V := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hdiff
    have heq : x - raws.getD i 0 = (P : ℤ) * ((x - raws.getD i 0) / (P : ℤ)) := (Int.mul_ediv_cancel' hdiv).symm
    have hdivcall := LightTernaryDivide.meets (d := d + 1) hdivide hdecode μ F ha heq (by omega)
    have hpW : (P : ℤ) ≤ lim.word := by have hh := F.word; omega
    have hworkW : (work : ℤ) ≤ lim.word := by have hh := F.free; have hh' := F.space; omega
    have hvW : (V : ℤ) ≤ lim.word := by have hh := F.word; omega
    have hdiffBounds := abs_le.mp hdiff
    have hxBounds := abs_le.mp hx
    have hrawBounds := abs_le.mp htarget
    have hpos : ((raws.getD i 0).toNat : ℤ) ≤ lim.word := by omega
    have hneg : ((-raws.getD i 0).toNat : ℤ) ≤ lim.word := by omega
    have hlit := Int.toNat_sub_toNat_neg (raws.getD i 0)
    have hchildSpace : cursor + 3 * C ^ j ≤ work :=
      by
      have hh : 3 * C ^ j ≤ 3 * (is.length + 1) * C ^ j := Nat.mul_le_mul_right _ (by omega)
      simp only [List.length_cons] at hs
      omega
    have hquot := child_target_bound P V hp hx htarget hdiv
    have hquotBounds := abs_le.mp hquot
    simp only [List.getD] at hdiffBounds hrawBounds hpos hneg hlit hquotBounds
    (obtain ⟨⟩ := _root_.id F)
    simp only [List.getD] at *
    rw [recordSteps]
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
      | refine _root_.Light.Ends.callToThen (hdivcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hdivcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSignedFiniteTable.literal, hlit, stepCost, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSignedFiniteTable.literal, hlit, stepCost, time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSignedFiniteTable.literal, hlit,
              stepCost, time] <;> omega)
      on_goal -1 => (rintro q' ν ⟨hq', hkeepD⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hcc := hchild i (hall i (by simp)) cursor ν hchildSpace
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
      | refine _root_.Light.Ends.callToThen (hcc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hq', stepCost, time,
              LightSignedFiniteTable.literal]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hq', stepCost, time, LightSignedFiniteTable.literal] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hq', stepCost, time,
              LightSignedFiniteTable.literal] <;> omega)
      on_goal -1 => (rintro result ξ ⟨hr, hseg, hkeepC⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    let children :=
      wantedCodes (P : ℤ) raws words maps j ((x - raws.getD i 0) / (P : ℤ)) R S (code + scale * words.getD i 0)
        (scale * R) (mapCode + mapScale * maps.getD i 0) (mapScale * S)
    have hlen : children.length ≤ C ^ j := by
      simpa [children, wantedCodes_length] using wantedOutputs_length_le (P : ℤ) raws C hcap j _
    have hsTail : cursor + 3 * children.length + 3 * is.length * C ^ j ≤ work :=
      by
      simp only [List.length_cons] at hs
      have hm := Nat.mul_le_mul_left 3 hlen
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at hs
      omega
    have ht := ih (fun a ha => hall a (by simp [ha])) (cursor + 3 * children.length) q' residue ξ hsTail
    change Seg ξ cursor (rowCells original children) at hseg
    change result = ((cursor + 3 * children.length : ℕ) : ℤ) at hr
    simp only [setLocal, hr]
    apply ht.mono (by simp [stepCost, LightSignedFiniteTable.literal, Expr.cost, List.length_cons, Nat.add_mul]; omega)
    rintro σ ⟨q'', hloc, hsegT, hkeepT⟩
    refine ⟨q'', ?_, ?_, ?_⟩
    ·
      simpa only [branchCodes, List.flatMap_cons, List.length_append, children, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Int.mul_add, Int.add_assoc] using hloc
    · simp only [branchCodes, List.flatMap_cons, rowCells_append]
      apply seg_append.mpr
      constructor
      · change Seg σ.mem cursor (rowCells original children)
        intro a ha
        rw [hkeepT (cursor + a) (by rw [rowCells_length] at ha; omega)]
        exact hseg a ha
      · simpa only [rowCells_length, branchCodes] using hsegT
    · intro a ha
      rw [hkeepT a (by omega), hkeepC a ha, hkeepD a (by omega)]
end ThreeSum.LightTernaryWantedCanonical
