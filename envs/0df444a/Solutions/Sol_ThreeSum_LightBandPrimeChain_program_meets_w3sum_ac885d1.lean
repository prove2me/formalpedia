-- Prove2me | solution 1 for ThreeSum.LightBandPrimeChain.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:41.923946+00:00
-- url     : https://prove2.me/submissions/7f8d022e-62b2-4bd1-97fb-9f6e3a43a8c1

import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
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
import Theorems.Thm_ThreeSum_BandPrimeChoice_chosenPrime_congr
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_pos
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
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
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeMinimum_maxMod_le_word
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_pos
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenPrime_congr
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BandWeightedScore.partialScore_zero
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeChain
open Light BandCandidateRows BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}
namespace ThreeSum.LightBandPrimeChain
theorem _root_.solution (primes : ℕ → ℕ) (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s) (hg : 0 < g)
    (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free)
    (haux : aux + s ≤ free) (hspace : space free maxMod g U levels ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 8 ≤ lim.depth) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y ^ (levels + 1) ≤ maxMod) :
    Meets lim program 18 d [a, b, c, nA, nB, nC, g, recs, rs.length, aux, s, levels, free] μ
      (time maxMod g rs.length s U levels)
      (fun result ν =>
        result =
            (modulus primes s nA nB nC g (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) rs levels : ℤ) ∧
          (∀ i ≤ levels,
              ν (free + i) =
                (modulus primes s nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) rs i : ℤ)) ∧
            Kept μ ν free) :=
  by
  let A := fun i => μ (a + i)
  let B := fun i => μ (b + i)
  let C := fun i => μ (c + i)
  let qs := modulus primes s nA nB nC g A B C rs
  let ct := LightBandPrimeMinimum.time maxMod g rs.length s U
  have hwork : free + levels + 1 ≤ lim.space :=
    by
    have hh := (le_max_right _ _).trans hspace
    change free + levels + 1 + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    omega
  have hY : 1 ≤ Y := (hprime 0 hs).one_lt.le.trans (hhi 0 hs)
  have hqpos (i : ℕ) : 0 < qs i := modulus_pos primes A B C rs hs hprime i
  have hqhi (i : ℕ) : qs i ≤ Y ^ i := (modulus_bounds primes A B C rs hs 0 Y i (fun _ _ => Nat.zero_le _) hhi).2
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length s U)).trans hword
  have hqWord (i : ℕ) (hi : i ≤ levels) : (qs i : ℤ) ≤ lim.word :=
    by
    have hh : qs i ≤ maxMod := (hqhi i).trans ((Nat.pow_le_pow_right hY (by omega : i ≤ levels + 1)).trans hmax)
    exact (Int.ofNat_le.mpr hh).trans hmaxWord
  have hproducts (i : ℕ) (hi : i < levels) : ∀ j < s, ∀ k < s, qs i * primes j * primes k ≤ maxMod :=
    by
    intro j hj k hk
    calc
      _ ≤ Y ^ i * Y * Y := Nat.mul_le_mul (Nat.mul_le_mul (hqhi i) (hhi j hj)) (hhi k hk)
      _ = Y ^ (i + 2) := by simp [pow_succ]
      _ ≤ Y ^ (levels + 1) := (Nat.pow_le_pow_right hY (by omega))
      _ ≤ maxMod := hmax
  apply Meets.of_body (p := 18) (by rfl : program[18]? = some (body 17))
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + levels + 1) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen free (1 : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := levels * (ct + 140) + 20) (Q := Inv μ qs a b c nA nB nC g recs rs.length aux s levels free levels)
        (Inv μ qs a b c nA nB nC g recs rs.length aux s levels free) levels (ct + 110) ?start ?round ?done ?bound (hT :=
        by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))))
      ?finish (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ct] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, Function.update μ free (1 : ℤ), ?_, ?_, ?_⟩
    · simp [qs, modulus, update_frame_setLocal]
    · intro j hj
      have hj0 : j = 0 := by omega
      simp [hj0, qs, modulus]
    · intro j hj
      exact Function.update_of_ne (by omega) _ _
  case round =>
    rintro i _ hi _ ⟨pval, ν, rfl, hwritten, hkept⟩
    have hrecordsν : Seg ν recs (cells rs) := by
      apply hrecords.congr
      intro j hj
      rw [cells_length] at hj
      exact hkept _ (by omega)
    have hAν : ∀ j < nA, |ν (a + j)| ≤ (U : ℤ) := by intro j hj; rw [hkept _ (by omega)]; exact hA j hj
    have hBν : ∀ j < nB, |ν (b + j)| ≤ (U : ℤ) := by intro j hj; rw [hkept _ (by omega)]; exact hB j hj
    have hCν : ∀ j < nC, |ν (c + j)| ≤ (U : ℤ) := by intro j hj; rw [hkept _ (by omega)]; exact hC j hj
    have hreadν : ∀ j < s, ν (aux + j) = (primes j : ℤ) := by intro j hj; exact (hkept _ (by omega)).trans (hread j hj)
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
            (((LightBandPrimeMinimum.program_meets (d := d + 1) (q := qs i) (free := free + levels + 1) primes rs hw
                    (by omega) hg (hqpos i) hs (by omega) (by omega) (by omega) (by omega) (by omega) hspace hword
                    hrecordsν hflag hvalid hAν hBν hCν hreadν hprime hinj (hproducts i hi)).append
                [body 17])
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            ((LightBandPrimeMinimum.program_meets (d := d + 1) (q := qs i) (free := free + levels + 1) primes rs hw
                  (by omega) hg (hqpos i) hs (by omega) (by omega) (by omega) (by omega) (by omega) hspace hword
                  hrecordsν hflag hvalid hAν hBν hCν hreadν hprime hinj (hproducts i hi)).append
              [body 17])
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hchosen :
      chosenPrime primes s (qs i) nA nB nC g (fun j => ν (a + j)) (fun j => ν (b + j)) (fun j => ν (c + j)) rs =
        chosenPrime primes s (qs i) nA nB nC g A B C rs :=
      chosenPrime_congr rs (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
        (fun j hj => hkept _ (by omega))
    rw [hchosen] at hresult
    subst result
    have hnext := hqWord (i + 1) (by omega)
    have hprodWord : (qs i : ℤ) * (chosenPrime primes s (qs i) nA nB nC g A B C rs : ℤ) ≤ lim.word := by
      simpa only [qs, modulus, Nat.cast_mul] using hnext
    have hprodNonneg : (0 : ℤ) ≤ (qs i : ℤ) * (chosenPrime primes s (qs i) nA nB nC g A B C rs : ℤ) := by positivity
    dsimp only [qs] at hprodWord hprodNonneg
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (qs (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, qs, modulus, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [qs, modulus, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, qs, modulus, ct] <;> omega)
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
      refine _root_.Light.Ends.storeToThen (free + i + 1) (qs (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, chosenPrime primes s (qs i) nA nB nC g A B C rs, Function.update ν₁ (free + i + 1) (qs (i + 1) : ℤ), ?_,
        ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro j hj
      by_cases heq : j = i + 1
      · simp [heq, Nat.add_assoc]
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep₁ _ (by omega)).trans (hwritten j (by omega))
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact (hkeep₁ _ (by omega)).trans (hkept j hj)
  case done =>
    intro σ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨pval, ν, rfl, hwritten, hkept⟩
    simp
  case finish =>
    rintro _ ⟨pval, ν, rfl, hwritten, hkept⟩
    have hfinal := hqWord levels le_rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (qs levels) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [qs, A, B, C], hwritten, hkept⟩
end ThreeSum.LightBandPrimeChain
