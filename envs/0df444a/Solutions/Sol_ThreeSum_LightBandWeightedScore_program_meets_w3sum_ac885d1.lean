-- Prove2me | solution 1 for ThreeSum.LightBandWeightedScore.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:46:58.728857+00:00
-- url     : https://prove2.me/submissions/0d6b64a0-4c2a-473e-bd9e-adc582f76218

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_pieceThen
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
import Theorems.Thm_ThreeSum_BandCandidateRows_seg_record
import Theorems.Thm_ThreeSum_BandWeightedScore_block_congr
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_bound
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_succ
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
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9ba359ecf22e73cc
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
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
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
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
open ThreeSum ThreeSum.LightBandWeightedScore
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
namespace ThreeSum.LightBandWeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 6 ≤ lim.depth) (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod) (ha : a + nA ≤ free)
    (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free) (haux : aux + s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) (hproduct : ∀ i < s, q * primes i ≤ maxMod) :
    Meets lim program 16 d [a, b, c, nA, nB, nC, g, recs, rs.length, q, aux, s, free] μ (time maxMod g rs.length s U)
      (fun result ν =>
        result = (score primes s q nA nB nC g (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) rs : ℤ) ∧
          Kept μ ν free) :=
  by
  let A := fun i => μ (a + i)
  let B := fun i => μ (b + i)
  let C := fun i => μ (c + i)
  let f := partialScore primes s q nA nB nC g A B C rs
  have hf0 : f 0 = 0 := partialScore_zero ..
  have hbudget (k : ℕ) (hk : k ≤ word maxMod nA nB nC g rs.length s U) : (k : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hk).trans hword
  have hcellWord := hbudget (LightBandWeightedScoreCell.word maxMod nA nB nC g s U) (by unfold word; omega)
  have htotalWord := hbudget (rs.length * (s * g ^ 3)) (by unfold word; omega)
  have hfWord (i : ℕ) (hi : i ≤ rs.length) : (f i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          ((partialScore_bound primes s q nA nB nC g A B C rs i hprime hinj).trans (Nat.mul_le_mul_right _ hi))).trans
      htotalWord
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    omega
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < rs.length) (hkeep : Kept μ ν free) :
    Meets lim program 15 (d + 1) [a, b, c, nA, nB, nC, g, recs + 4 * i, q, aux, s, free] ν
      (LightBandWeightedScoreCell.time maxMod g s U)
      (fun value ξ => value = (block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) ∧ Kept ν ξ free) :=
    by
    have hmem : rs.getD i default ∈ rs := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
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
      ((LightBandWeightedScoreCell.meets (d := d + 1) (μ := ν) LightBandWeightedScoreCell.programProcs (pMain := 15)
                (pLength := 14) rfl rfl primes (rs.getD i default) hw (by omega) hg hq hqmax ha hb hc (by omega) haux
                hspace hcellWord (seg_record hrecordsν hi) (hflag _ hmem) (hvalid _ hmem) hAν hBν hCν hreadν hprime hinj
                hproduct).append
            [body 15]).mono
        le_rfl ?_
    rintro value ξ ⟨hvalue, hkeep'⟩
    refine ⟨hvalue.trans ?_, hkeep'⟩
    congr 1
    exact
      block_congr _ (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega))
  apply Meets.of_body (p := 16) (by rfl : program[16]? = some (body 15))
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
      (Ends.for (T := rs.length * (LightBandWeightedScoreCell.time maxMod g s U + 100) + 6) (Q :=
        Inv μ f a b c nA nB nC g recs rs.length q aux s free rs.length)
        (Inv μ f a b c nA nB nC g recs rs.length q aux s free) rs.length
        (LightBandWeightedScoreCell.time maxMod g s U + 92) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, μ, ?_, fun _ _ => rfl⟩
    simp [update_frame_setLocal, hf0]
    exact (frame_append_zeros [a, b, c, nA, nB, nC, g, recs, rs.length, q, aux, s, free, 0, 0] 1).symm
  case round =>
    rintro i _ hi _ ⟨old, ν, rfl, hkeep⟩
    have hsum := partialScore_succ primes s q nA nB nC g A B C rs i
    change f (i + 1) = f i + block primes s q nA nB nC g A B C (rs.getD i default) at hsum
    have hfi := hfWord i (by omega)
    have hnext := hfWord (i + 1) (by omega)
    have hsumWord : (f i : ℤ) + (block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) ≤ lim.word :=
      by
      rw [hsum, Nat.cast_add] at hnext
      exact hnext
    have hsumNonneg : (0 : ℤ) ≤ (f i : ℤ) + (block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) :=
      add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    simp only [List.getD] at hsumWord hsumNonneg hsum
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
      on_goal -1 => (rintro value ξ ⟨hvalue, hkeep'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
      refine _root_.Light.Ends.setToThen (f (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hsum] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, (block primes s q nA nB nC g A B C (rs.getD i default) : ℤ), ξ, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · exact fun j hj => (hkeep' j hj).trans (hkeep j hj)
  case done =>
    rintro _ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨old, ν, rfl, hkeep⟩
    have hfi := hfWord i hi
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨old, ν, rfl, hkeep⟩
    have hf := hfWord rs.length le_rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (f rs.length : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, hkeep⟩
end ThreeSum.LightBandWeightedScore
