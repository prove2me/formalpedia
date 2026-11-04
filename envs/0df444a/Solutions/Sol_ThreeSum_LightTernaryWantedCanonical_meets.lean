-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedCanonical.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:50.696864+00:00
-- url     : https://prove2.me/submissions/96f6517a-ce80-47a6-a954-0b37ac704d49

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_leaf_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_recordSteps_ends
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_selector_ends
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
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
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
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
theorem _root_.solution {pMain pDivide pDecode pEmod P R S C V work : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P R S raws words maps))
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body) (hem : Prog[pEmod]? = some emodBody) (hp : 2 ≤ P)
    (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C) (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ)) (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S) (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2 * V) work) :
    ∀ (J d : ℕ) (x : ℤ) (code scale mapCode mapScale original dst : ℕ) (μ : ℕ → ℤ),
      |x| ≤ (V : ℤ) →
        (codeLimit R code scale J : ℤ) ≤ lim.word →
          (codeLimit S mapCode mapScale J : ℤ) ≤ lim.word →
            (original : ℤ) ≤ lim.word →
              (J : ℤ) ≤ lim.word →
                dst + 3 * C ^ J ≤ work →
                  d + J + 3 ≤ lim.depth →
                    Meets lim Prog pMain d [J, x, code, scale, mapCode, mapScale, original, dst, work] μ (time P C V J)
                      (fun r ν =>
                        r =
                            ((dst +
                                  3 * (wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale).length :
                                ℕ) :
                              ℤ) ∧
                          Seg ν dst
                              (rowCells original
                                (wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale)) ∧
                            Kept μ ν dst) :=
  by
  intro J
  induction J with
  | zero =>
    intro d x code scale mapCode mapScale original dst μ hx hc hm ho hJ hs hd
    have hw := F.space
    have hf := F.free
    have hs' : dst + 3 ≤ lim.space := by simp only [pow_zero] at hs; omega
    have hc' : (code : ℤ) ≤ lim.word :=
      by
      simp only [codeLimit, pow_zero, Nat.mul_one] at hc
      omega
    simpa [time, wantedCodes, wantedOutputs, encode, rowCells, TernaryWantedCanonicalPairs.rowCells] using
      leaf_meets (d := d) hmain x code scale mapCode mapScale original dst work μ hw hs' hc'
        (by simp only [codeLimit, pow_zero, Nat.mul_one] at hm; omega) ho
  | succ J ih =>
    intro d x code scale mapCode mapScale original dst μ hx hc hm ho hJ hs hd
    (obtain ⟨⟩ := _root_.id F)
    have hb := codeLimit_base (code := code) (scale := scale) (j := J + 1) hR
    have hcode : (code : ℤ) ≤ lim.word := by omega
    have hscale : (scale : ℤ) ≤ lim.word := by omega
    have hdst : (dst : ℤ) ≤ lim.word := by omega
    have hwork : (work : ℤ) ≤ lim.word := by omega
    have hP : (P : ℤ) ≤ lim.word := by omega
    have hx2 : |x| ≤ ((2 * V : ℕ) : ℤ) := by omega
    have hxBounds := abs_le.mp hx
    have hemod := emod_meets (d := d + 1) (μ := μ) (x := x) hem F hx2
    have hemodTime := LightResidues.emodTime_le (p := P) hx2
    simp only [emodTime, LightResidues.residueBudget, Nat.mul_comm] at hemodTime
    let r0 := (x % (P : ℤ)).toNat
    have hrcast : (r0 : ℤ) = x % (P : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hrlt : r0 < P := by
      have hh := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < P)
      omega
    have hrword : (r0 : ℤ) ≤ lim.word := by omega
    have hbuckets : localBucket (P : ℤ) raws (r0 : ℤ) = localBucket (P : ℤ) raws x :=
      by
      apply localBucket_eq_of_emod raws
      rw [hrcast, Int.emod_emod]
    have hlength := wantedOutputs_length_le (P : ℤ) raws C hcap (J + 1) x
    have hcodesLength :
      (wantedCodes (P : ℤ) raws words maps (J + 1) x R S code scale mapCode mapScale).length ≤ C ^ (J + 1) := by
      simpa only [wantedCodes_length] using hlength
    have houtWord :
      ((dst + 3 * (wantedCodes (P : ℤ) raws words maps (J + 1) x R S code scale mapCode mapScale).length : ℕ) : ℤ) ≤
        lim.word :=
      by
      have hh := Nat.mul_le_mul_left 3 hcodesLength
      omega
    apply Meets.of_body hmain
    unfold body
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen (0 < J + 1) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, overhead]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, overhead] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, overhead] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (hemod _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hemod ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, overhead,
                emodTime, LightResidues.residueBudget, Nat.mul_comm]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, overhead, emodTime, LightResidues.residueBudget, Nat.mul_comm] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, overhead, emodTime,
                LightResidues.residueBudget, Nat.mul_comm] <;> omega)
        on_goal -1 => (rintro remainder ν ⟨hrem, hkeepE⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, overhead,
                emodTime, LightResidues.residueBudget, Nat.mul_comm]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, overhead, emodTime, LightResidues.residueBudget, Nat.mul_comm] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, overhead, emodTime,
                LightResidues.residueBudget, Nat.mul_comm] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      simp only [setLocal]
      have hchildren :
        ∀ i ∈ localBucket (P : ℤ) raws x,
          ∀ (start : ℕ) (ξ : ℕ → ℤ),
            start + 3 * C ^ J ≤ work →
              Meets lim Prog pMain (d + 1)
                [J, (x - raws.getD i 0) / (P : ℤ), code + scale * words.getD i 0, scale * R,
                  mapCode + mapScale * maps.getD i 0, mapScale * S, original, start, work]
                ξ (time P C V J)
                (fun r ζ =>
                  r =
                      ((start +
                            3 *
                              (wantedCodes (P : ℤ) raws words maps J ((x - raws.getD i 0) / (P : ℤ)) R S
                                  (code + scale * words.getD i 0) (scale * R) (mapCode + mapScale * maps.getD i 0)
                                  (mapScale * S)).length :
                          ℕ) :
                        ℤ) ∧
                    Seg ζ start
                        (rowCells original
                          (wantedCodes (P : ℤ) raws words maps J ((x - raws.getD i 0) / (P : ℤ)) R S
                            (code + scale * words.getD i 0) (scale * R) (mapCode + mapScale * maps.getD i 0)
                            (mapScale * S))) ∧
                      Kept ξ ζ start) :=
        by
        intro i hi start ξ hs'
        obtain ⟨hi', hdiv⟩ := (mem_localBucket _ _ _ _).mp hi
        apply
          ih (d + 1) _ _ _ _ _ original start ξ (child_target_bound P V hp hx (hraw i hi') hdiv)
            ((Int.ofNat_le.mpr (codeLimit_child hR (hwords i hi'))).trans hc)
            ((Int.ofNat_le.mpr (codeLimit_child hS (hmaps i hi'))).trans hm) ho (by omega) hs' (by omega)
      have hrec :=
        recordSteps_ends (d := d) hdivide hdecode hp hN hR hS hcap hraw hwords hmaps x code scale mapCode mapScale
          original dst work F hx hc hm ho hJ hRW hSW hNW (by omega) hchildren (localBucket (P : ℤ) raws x)
          (fun _ h => h) dst (0 : ℤ) remainder ν
          (by
            have hh := Nat.mul_le_mul_right (3 * C ^ J) (hcap x)
            rw [pow_succ'] at hs
            nlinarith)
      let Q := fun σ : State =>
        ∃ q',
          σ.loc =
              frame
                [J + 1, x, code, scale, mapCode, mapScale, original, dst, work, q',
                  dst + 3 * (wantedCodes (P : ℤ) raws words maps (J + 1) x R S code scale mapCode mapScale).length,
                  remainder] ∧
            Seg σ.mem dst
                (rowCells original (wantedCodes (P : ℤ) raws words maps (J + 1) x R S code scale mapCode mapScale)) ∧
              Kept ν σ.mem dst
      have hrec' :
        Ends lim Prog d (recordSteps pMain pDivide P R S raws words maps (localBucket (P : ℤ) raws x))
          ⟨frame [J + 1, x, code, scale, mapCode, mapScale, original, dst, work, 0, dst, remainder], ν⟩
          (C * (stepCost V + time P C V J)) Q :=
        by
        apply hrec.mono (Nat.mul_le_mul_right _ (hcap x))
        intro σ hσ
        simpa only [Q, branchCodes, ← wantedCodes_succ] using hσ
      have hsel :=
        selector_ends (d := d) (pSelf := pMain) (pDivide := pDivide) (P := P) (R := R) (S := S) (raws := raws) (words :=
          words) (maps := maps) (Prog := Prog) (T := C * (stepCost V + time P C V J))
          [J + 1, x, code, scale, mapCode, mapScale, original, dst, work, 0, dst, remainder] ν Q
          (by simp [frame, hrem, hrcast]) hrword (List.range P) (by simp [hrlt])
          (fun r hr => by have hh := List.mem_range.mp hr; omega)
          (fun r hr he => by subst r; simpa only [hbuckets] using hrec')
      focus
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        | refine _root_.Light.Ends.pieceThen hsel ?_ ?_
        | refine _root_.Light.Ends.pieceLast hsel ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, overhead,
                emodTime, LightResidues.residueBudget, Nat.mul_comm]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, overhead, emodTime, LightResidues.residueBudget, Nat.mul_comm] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => rintro σ ⟨q', hloc, hseg, hkeepS⟩
      cases σ with
      | mk loc mem =>
        dsimp only at hloc hseg hkeepS ⊢
        subst loc
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
            _root_.Light.Ends.setToThen
              (dst + 3 * (wantedCodes (P : ℤ) raws words maps (J + 1) x R S code scale mapCode mapScale).length : ℕ) ?_
              ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, overhead,
                  emodTime, LightResidues.residueBudget, Nat.mul_comm]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, overhead, emodTime, LightResidues.residueBudget, Nat.mul_comm] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, overhead, emodTime,
                  LightResidues.residueBudget, Nat.mul_comm] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        refine ⟨rfl, hseg, ?_⟩
        intro a ha
        change mem a = μ a
        rw [hkeepS a ha, hkeepE a (by omega)]
    · omega
end ThreeSum.LightTernaryWantedCanonical
