-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPrimeCore.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:27:45.034519+00:00
-- url     : https://prove2.me/submissions/4a201bfe-6ff3-42e9-965b-51eec85c4687

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_read
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
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_congr
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
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_modulus_bounds
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_984b86210e82afdf
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeMinimum_maxMod_le_word
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9ba359ecf22e73cc
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_congr
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Theorems.Thm_ThreeSum_LightPrimePool_prime_injective
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_size_le
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
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
open ThreeSum ThreeSum.LightEncodedColorPrimeCore
open Light BandCandidateRows EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs M y free maxMod U : ℕ}
namespace ThreeSum.LightEncodedColorPrimeCore
theorem _root_.solution (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free)
    (hspace : space free maxMod g M y U ≤ lim.space) (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 9 ≤ lim.depth) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hmax : (4 * y) ^ (LightBandPrimeDepth.depth M y + 1) ≤ maxMod) :
    Meets lim program 23 d [a, b, c, nA, nB, nC, g, recs, rs.length, M, y, free] μ (time maxMod g rs.length M y U)
      (fun result ν =>
        result =
            (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs (LightBandPrimeDepth.depth M y) :
              ℤ) ∧
          EncodedColorPrimeData.Stored ν free M y
              (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs) ∧
            Kept μ ν free) :=
  by
  let qs :=
    LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) rs
  have hdWord : (LightBandPrimeDepth.word M y : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hpWord : (LightPrimePool.word y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hcWord : (LightBandWeightedScore.word maxMod nA nB nC g rs.length (LightPrimePool.size y) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hpSpace : LightPrimePool.space (poolBase free) y ≤ lim.space := (le_max_left _ _).trans hspace
  have hcSpace : LightBandPrimeChain.space (prefixBase free y) maxMod g U (LightBandPrimeDepth.depth M y) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hpoolEnd : free + 6 + 3 * y ≤ lim.space := by unfold LightPrimePool.space poolBase at hpSpace; omega
  have hnext : nextFree free M y ≤ lim.space :=
    by
    have hh := (le_max_right _ _).trans hcSpace
    change prefixBase free y + LightBandPrimeDepth.depth M y + 1 + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    exact (Nat.le_add_right _ _).trans hh
  have hnext' : free + 6 + 3 * y + LightBandPrimeDepth.depth M y + 1 ≤ lim.space := hnext
  have hnextAddress : prefixBase free y + LightBandPrimeDepth.depth M y + 1 ≤ lim.space := hnext
  have hsize := LightPrimePool.size_le y
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length (LightPrimePool.size y) U)).trans
      hcWord
  have hqBound :=
    (LightBandPrimeConstruction.modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) (fun j => μ (a + j))
        (fun j => μ (b + j)) (fun j => μ (c + j)) rs (LightBandPrimeDepth.depth M y) hy).2
  have hqMax : qs (LightBandPrimeDepth.depth M y) ≤ maxMod :=
    hqBound.trans ((Nat.pow_le_pow_right (by omega : 1 ≤ 4 * y) (Nat.le_succ _)).trans hmax)
  have hqWord : (qs (LightBandPrimeDepth.depth M y) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqMax).trans hmaxWord
  apply Meets.of_body (p := 23) (by rfl : program[23]? = some (body 0 1 22))
  unfold body time
  have hDepth :=
    (((LightBandPrimeDepth.program_meets (d := d + 1) (μ := μ) hy hdWord).append
              (LightPrimePool.program.map (ReportingHostRelocation.relocate 1))).append
          (LightBandPrimeChain.program.map (ReportingHostRelocation.relocate 4))).append
      [body 0 1 22]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    first
    | refine _root_.Light.Ends.callToThen (hDepth _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hDepth ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro levels μ₀ ⟨hlevels, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₀
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.setToThen (poolBase free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, poolBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [poolBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, poolBase] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hPool :=
    ((ReportingHostRelocation.meets
              (LightPrimePool.program_meets (d := d + 1) (μ := μ) (y := y) (free := poolBase free) hw (by omega) hy
                hpSpace hpWord)
              LightBandPrimeDepth.program).append
          (LightBandPrimeChain.program.map (ReportingHostRelocation.relocate 4))).append
      [body 0 1 22]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    first
    | refine _root_.Light.Ends.callToThen (hPool _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hPool ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro count μ₁ ⟨hcount, hpool, keepPool⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst count
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.setToThen (prefixBase free y : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, prefixBase, poolBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [prefixBase, poolBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, prefixBase, poolBase] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have records₁ : Seg μ₁ recs (cells rs) := by
    apply hrecords.congr
    intro i hi
    rw [cells_length] at hi
    exact keepPool _ (by unfold poolBase; omega)
  have valuesA₁ : ∀ i < nA, |μ₁ (a + i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]
    exact hA i hi
  have valuesB₁ : ∀ i < nB, |μ₁ (b + i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]
    exact hB i hi
  have valuesC₁ : ∀ i < nC, |μ₁ (c + i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]
    exact hC i hi
  have hChain :=
    (ReportingHostRelocation.meets
          (LightBandPrimeChain.program_meets (d := d + 1) (μ := μ₁) (aux := poolBase free) (free := prefixBase free y)
            (Y := 4 * y) (LightPrimePool.prime y) rs hw (LightPrimePool.size_pos hy) hg
            (by unfold prefixBase poolBase; omega) (by unfold prefixBase poolBase; omega)
            (by unfold prefixBase poolBase; omega) (by unfold prefixBase poolBase; omega) (by unfold prefixBase; omega)
            hcSpace hcWord (by omega) records₁ hflag hvalid valuesA₁ valuesB₁ valuesC₁ (fun i hi => hpool.read hi)
            (fun i hi => (LightPrimePool.prime_spec hi).1)
            (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
            (fun i hi => (LightPrimePool.prime_spec hi).2.2) hmax)
          poolProgram).append
      [body 0 1 22]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    first
    | refine _root_.Light.Ends.callToThen (hChain _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hChain ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlevels]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlevels] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlevels] <;> omega)
    on_goal -1 =>
      (rintro result μ₂ ⟨hresult, hprefix, keepChain⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmod (i : ℕ) :
    BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y) nA nB nC g (fun j => μ₁ (a + j))
        (fun j => μ₁ (b + j)) (fun j => μ₁ (c + j)) rs i =
      qs i :=
    BandPrimeChoice.modulus_congr rs (fun j hj => keepPool _ (by unfold poolBase; omega))
      (fun j hj => keepPool _ (by unfold poolBase; omega)) (fun j hj => keepPool _ (by unfold poolBase; omega)) i
  have hresult' : result = (qs (LightBandPrimeDepth.depth M y) : ℤ) := by rw [hresult, hmod]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.setToThen (nextFree free M y : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, nextFree, hlevels]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [nextFree, hlevels] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, nextFree, hlevels] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen free (qs (LightBandPrimeDepth.depth M y) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hresult'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen (free + 1) (LightBandPrimeDepth.depth M y : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlevels]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hlevels] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlevels] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen (free + 2) (nextFree free M y : ℕ) ?_ ?_ ?_
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
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen (free + 3) (poolBase free : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, poolBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [poolBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, poolBase] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen (free + 4) (LightPrimePool.size y : ℕ) ?_ ?_ ?_
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
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.storeToThen (free + 5) (prefixBase free y : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, prefixBase, poolBase]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [prefixBase, poolBase] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, prefixBase, poolBase] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      ((repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)))
    refine _root_.Light.Ends.setToThen (qs (LightBandPrimeDepth.depth M y) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hresult'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hi' : i < 6 := by simpa only [values, List.length_cons, List.length_nil] using hi
    interval_cases i <;> simp [values, qs]
  · dsimp only
    apply hpool.congr
    intro i hi
    have hi' : i < LightPrimePool.size y := by simpa only [LightPrimePool.size, List.length_map] using hi
    repeat' rw [Function.update_of_ne (by unfold poolBase; omega)]
    exact keepChain _ (by unfold prefixBase; omega)
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by unfold prefixBase poolBase; omega)]
    exact (hprefix i hi).trans (congrArg Int.ofNat (hmod i))
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keepChain i (by unfold prefixBase poolBase; omega)).trans (keepPool i (by unfold poolBase; omega))
end ThreeSum.LightEncodedColorPrimeCore
