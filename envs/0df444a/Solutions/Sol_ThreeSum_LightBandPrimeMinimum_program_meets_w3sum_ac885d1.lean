-- Prove2me | solution 1 for ThreeSum.LightBandPrimeMinimum.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:55:53.403804+00:00
-- url     : https://prove2.me/submissions/98201fcc-f713-48e4-8e4f-db214b7cfe62

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Theorems.Thm_ThreeSum_LightBandPrimeMinimum_maxMod_le_word
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_Seg_congr
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
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_zero
import Theorems.Thm_ThreeSum_BandWeightedScore_score_bound
import Theorems.Thm_ThreeSum_BandWeightedScore_score_congr
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
import Theorems.Thm_ThreeSum_LightMinimum_least_lt
import Theorems.Thm_ThreeSum_LightMinimum_least_lt_of_le
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_score_congr
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
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
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
namespace ThreeSum.LightBandPrimeMinimum
theorem _root_.solution (primes : ℕ → ℕ) (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 7 ≤ lim.depth) (hg : 0 < g) (hq : 0 < q) (hs : 0 < s) (ha : a + nA ≤ free)
    (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free) (haux : aux + s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hrecords : Seg μ recs (cells rs)) (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q * primes i * primes j ≤ maxMod) :
    Meets lim program 17 d [a, b, c, nA, nB, nC, g, recs, rs.length, q, aux, s, free] μ (time maxMod g rs.length s U)
      (fun result ν =>
        result =
            (chosenPrime primes s q nA nB nC g (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) rs : ℤ) ∧
          Kept μ ν free) :=
  by
  let A := fun i => μ (a + i)
  let B := fun i => μ (b + i)
  let C := fun i => μ (c + i)
  let f := candidateScore primes s q nA nB nC g A B C rs
  let ct := LightBandWeightedScore.time maxMod g rs.length s U
  have htotal : rs.length * (s * g ^ 3) ≤ LightBandWeightedScore.word maxMod nA nB nC g rs.length s U :=
    by
    unfold LightBandWeightedScore.word
    omega
  have htotalWord : ((rs.length * (s * g ^ 3) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr htotal).trans hword
  have hf (i : ℕ) : 0 ≤ f i ∧ f i ≤ lim.word := by
    constructor
    · exact Int.natCast_nonneg _
    · exact (Int.ofNat_le.mpr (score_bound primes s (q * primes i) nA nB nC g A B C rs hprime hinj)).trans htotalWord
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (maxMod_le_word maxMod nA nB nC g rs.length s U)).trans hword
  have hqiMax (i : ℕ) (hi : i < s) : q * primes i ≤ maxMod :=
    (Nat.le_mul_of_pos_right _ (hprime 0 hs).pos).trans (hproduct i hi 0 hs)
  have hpiWord (i : ℕ) (hi : i < s) : (primes i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((Nat.le_mul_of_pos_left (primes i) hq).trans (hqiMax i hi))).trans hmaxWord
  have hqiWord (i : ℕ) (hi : i < s) : (q : ℤ) * (primes i : ℤ) ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (hqiMax i hi)).trans hmaxWord
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    omega
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < s) (hkeep : Kept μ ν free) :
    Meets lim program 16 (d + 1) [a, b, c, nA, nB, nC, g, recs, rs.length, q * primes i, aux, s, free] ν ct
      (fun value ξ => value = f i ∧ Kept ν ξ free) :=
    by
    have hrecordsν : Seg ν recs (cells rs) := by
      apply hrecords.congr
      intro j hj
      rw [cells_length] at hj
      exact hkeep _ (by omega)
    have hAν : ∀ j < nA, |ν (a + j)| ≤ (U : ℤ) := by intro j hj; rw [hkeep _ (by omega)]; exact hA j hj
    have hBν : ∀ j < nB, |ν (b + j)| ≤ (U : ℤ) := by intro j hj; rw [hkeep _ (by omega)]; exact hB j hj
    have hCν : ∀ j < nC, |ν (c + j)| ≤ (U : ℤ) := by intro j hj; rw [hkeep _ (by omega)]; exact hC j hj
    have hreadν : ∀ j < s, ν (aux + j) = (primes j : ℤ) := by intro j hj; rw [hkeep _ (by omega)]; exact hread j hj
    refine
      ((LightBandWeightedScore.program_meets (d := d + 1) (μ := ν) primes rs hw (by omega) hg
                (Nat.mul_pos hq (hprime i hi).pos) (hqiMax i hi) ha hb hc hrecs haux hspace hword hrecordsν hflag hvalid
                hAν hBν hCν hreadν hprime hinj (hproduct i hi)).append
            [body 16]).mono
        le_rfl ?_
    rintro value ξ ⟨hvalue, hkeep'⟩
    refine ⟨hvalue.trans ?_, hkeep'⟩
    unfold f candidateScore
    congr 1
    exact
      score_congr rs (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega))
  have hp0 := hpiWord 0 hs
  have hq0 := hqiWord 0 hs
  have hq0Nonneg : (0 : ℤ) ≤ (q : ℤ) * (primes 0 : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hread0 : μ aux = (primes 0 : ℤ) := by simpa only [Nat.add_zero] using hread 0 hs
  apply Meets.of_body (p := 17) (by rfl : program[17]? = some (body 16))
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
    first
    | refine _root_.Light.Ends.callToThen ((hcall μ 0 hs (fun _ _ => rfl)) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hcall μ 0 hs (fun _ _ => rfl)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread0, ct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hread0, ct] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread0, ct] <;> omega)
    on_goal -1 => (rintro value μ₁ ⟨hvalue, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst value
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
      (Ends.for (T := s * (ct + 140) + 30) (Q := Inv μ f a b c nA nB nC g recs rs.length q aux s free s)
        (Inv μ f a b c nA nB nC g recs rs.length q aux s free) s (ct + 110) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, μ₁, ?_, hkeep₁⟩
    simp only [LightMinimum.least, update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc, μ₁⟩ : State)) (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨old, ν, rfl, hkeep⟩
    have hbest : LightMinimum.least f i < s := LightMinimum.least_lt_of_le f hs (by omega)
    have hpi := hpiWord i hi
    have hqi := hqiWord i hi
    have hqiNonneg : (0 : ℤ) ≤ (q : ℤ) * (primes i : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hreadν : ν (aux + i) = (primes i : ℤ) := (hkeep _ (by omega)).trans (hread i hi)
    have hfi := hf i
    have hfb := hf (LightMinimum.least f i)
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
      | refine _root_.Light.Ends.callToThen ((hcall ν i hi hkeep) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hcall ν i hi hkeep) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadν, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadν, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadν, ct] <;> omega)
      on_goal -1 => (rintro value ξ ⟨hvalue, hkeep'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst value
    have hkept : Kept μ ξ free := fun j hj => (hkeep' j hj).trans (hkeep j hj)
    refine
      Ends.iteLast (fun hcmp => ?_) (fun hcmp => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    · have hcmp' : f i < f (LightMinimum.least f i) := by simpa using hcmp
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen (f i) ?_ ?_ ?_
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
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen (i : ℕ) ?_ ?_ ?_
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
      refine ⟨by simp, f i, ξ, ?_, hkept⟩
      simp [LightMinimum.least, hcmp', update_frame_setLocal]
    · have hcmp' : ¬f i < f (LightMinimum.least f i) := by simpa using hcmp
      apply Ends.skip
      refine ⟨by simp, f i, ξ, ?_, hkept⟩
      simp [LightMinimum.least, hcmp', update_frame_setLocal]
  case done =>
    intro σ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨old, ν, rfl, hkeep⟩
    simp
  case finish =>
    rintro _ ⟨old, ν, rfl, hkeep⟩
    have hbest : LightMinimum.least f s < s := LightMinimum.least_lt f hs
    have hbestWord := hpiWord (LightMinimum.least f s) hbest
    have hreadBest : ν (aux + LightMinimum.least f s) = (primes (LightMinimum.least f s) : ℤ) :=
      (hkeep _ (by omega)).trans (hread _ hbest)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (primes (LightMinimum.least f s) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadBest, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadBest, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadBest, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [chosenPrime, chosenIndex, f, A, B, C], hkeep⟩
end ThreeSum.LightBandPrimeMinimum
