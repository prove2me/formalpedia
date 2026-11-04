-- Prove2me | solution 1 for ThreeSum.LightWantedSetup.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:11.984207+00:00
-- url     : https://prove2.me/submissions/6cfd7d24-efc2-416e-97e1-695a3ffa08a7

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
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
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
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
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_f152642222afc127
import Theorems.Thm_ThreeSum_WantedPairs_pairs_length
import Definitions.Def_WeightedCache3SUM_Alias_f9de9277dde47511
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Theorems.Thm_ThreeSum_WantedResidueKeys_code_eq_iff
import Theorems.Thm_ThreeSum_WantedResidueKeys_code_lt
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
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightWantedSetup
theorem _root_.solution {μ : ℕ → ℤ} {a b NL NR M free U D d : ℕ} {shift : ℤ} (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M) (ha : a + NL ≤ free) (hb : b + NR ≤ free)
    (hspace : space free M left right NL NR U D shift ≤ lim.space)
    (hword : (LightSourceResidues.word M M U D : ℤ) ≤ lim.word) (hshift : |shift| ≤ (D : ℤ))
    (hd : d + NL + 5 ≤ lim.depth) (hleft : ∀ i < NL, μ (a + i) = left i) (hright : ∀ j < NR, μ (b + j) = right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ)) (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 11 d [a, b, NL, NR, M, shift, free] μ (time M left right NL NR U D shift)
      (fun r ν => r = (free : ℤ) ∧ Output ν free M left right NL NR shift ∧ Kept μ ν free) :=
  by
  let lc := leftCodes free
  let rc := rightCodes free NL
  let bb := bucketBase free NL NR
  let off := LightSourceBucketSetup.offsets bb M
  let flat := LightSourceBucketSetup.flat bb M
  let dst := pairBase free NL NR M
  let lkey := fun i => code M shift (left i)
  let rkey := fun j => code M 0 (right j)
  have hjoinTime :
    LightWantedJoin.time lkey rkey NR NL =
      LightWantedJoin.time (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL :=
    rfl
  have hscanSpace : LightSourceResidues.space dst M U D ≤ lim.space := (le_max_left _ _).trans hspace
  have hpairSpace : dst + 2 * total M left right NL NR shift ≤ lim.space := (le_max_right _ _).trans hspace
  have hdst : dst = free + 4 + NL + NR + 3 * M + 1 + NR := rfl
  have hlc : lc = free + 4 := rfl
  have hrc : rc = free + 4 + NL := rfl
  have hbb : bb = free + 4 + NL + NR := rfl
  have hoff : off = bb + M := rfl
  have hflat : flat = bb + 3 * M + 1 := rfl
  have h3M : (3 * (M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3 * M ≤ lim.space by omega) : (3 * (M : ℤ)) ≤ lim.space).trans hw
  have hDWord : (D : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold LightSourceResidues.word; omega)).trans hword
  have hlkey : ∀ i < NL, lkey i < M := fun _ _ => code_lt hM _ _
  have hrkey : ∀ j < NR, rkey j < M := fun _ _ => code_lt hM _ _
  apply Meets.of_body (p := 11) (by rfl : program[11]? = some (body 0 2 9))
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
    refine _root_.Light.Ends.setToThen (lc : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lc, leftCodes]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [lc, leftCodes] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lc, leftCodes] <;> omega)
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
    refine _root_.Light.Ends.setToThen (rc : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rc, rightCodes, lc]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rc, rightCodes, lc] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rc, rightCodes, lc] <;> omega)
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
    refine _root_.Light.Ends.setToThen (bb : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bb, bucketBase, rc]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [bb, bucketBase, rc] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bb, bucketBase, rc] <;> omega)
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
    refine _root_.Light.Ends.setToThen (off : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, off, LightSourceBucketSetup.offsets]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [off, LightSourceBucketSetup.offsets] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, off, LightSourceBucketSetup.offsets] <;> omega)
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
    refine _root_.Light.Ends.setToThen (flat : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flat, LightSourceBucketSetup.flat]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [flat, LightSourceBucketSetup.flat] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flat, LightSourceBucketSetup.flat] <;> omega)
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
    refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dst, pairBase, LightSourceBucketSetup.next,
            flat]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [dst, pairBase, LightSourceBucketSetup.next, flat] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dst, pairBase, LightSourceBucketSetup.next,
            flat] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hsL :=
    (((LightSourceResidues.program_meets (d := d + 1) (μ := μ) (src := a) (dst := lc) (n := NL) (p := M) (m := M)
                  (work := dst) (U := U) (D := D) (shift := shift) hw (by omega) hM hM (by omega) (by omega) hscanSpace
                  (Or.inl (by omega)) hshift hword (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)).append
              (LightSourceBucketSetup.program.map (ReportingHostRelocation.relocate 2))).append
          (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append
      [body 0 2 9]
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
    | refine _root_.Light.Ends.callToThen (hsL _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsL ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, code]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [code] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, code] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hcodesL, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadL (i : ℕ) (hi : i < NL) : μ₁ (lc + i) = (lkey i : ℤ) :=
    by
    rw [hcodesL i hi, hleft i hi]
    rfl
  have hsR :=
    (((LightSourceResidues.program_meets (d := d + 1) (μ := μ₁) (src := b) (dst := rc) (n := NR) (p := M) (m := M)
                  (work := dst) (U := U) (D := D) (shift := 0) hw (by omega) hM hM (by omega) (by omega) hscanSpace
                  (Or.inl (by omega)) (by simp) hword
                  (fun j hj => by rw [hkeepL _ ⟨by omega, Or.inl (by omega)⟩, hright j hj]; exact hvaluesR j hj)).append
              (LightSourceBucketSetup.program.map (ReportingHostRelocation.relocate 2))).append
          (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append
      [body 0 2 9]
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
    | refine _root_.Light.Ends.callToThen (hsR _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsR ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, code]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [code] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, code] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hcodesR, hkeepR⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadR (j : ℕ) (hj : j < NR) : μ₂ (rc + j) = (rkey j : ℤ) :=
    by
    rw [hcodesR j hj, hkeepL _ ⟨by omega, Or.inl (by omega)⟩, hright j hj]
    rfl
  have hleft₂ (i : ℕ) (hi : i < NL) : μ₂ (lc + i) = (lkey i : ℤ) :=
    (hkeepR _ ⟨by omega, Or.inl (by omega)⟩).trans (hreadL i hi)
  have hbuckets :=
    ((ReportingHostRelocation.meets
              (LightSourceBucketSetup.programProcs.meets (d := d + 1) (μ := μ₂) (keys := rc) (N := NR) (M := M) (base :=
                bb) rkey hw (by omega) hM (by omega) (by change dst ≤ lim.space; omega) hrkey hreadR)
              LightSourceResidues.program).append
          (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append
      [body 0 2 9]
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
    | refine _root_.Light.Ends.callToThen (hbuckets _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hbuckets ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBucketSetup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBucketSetup.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBucketSetup.time] <;> omega)
    on_goal -1 => (rintro next μ₃ ⟨hnext, H, hcounts, hkeepB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hleft₃ (i : ℕ) (hi : i < NL) : μ₃ (lc + i) = (lkey i : ℤ) := (hkeepB _ (by omega)).trans (hleft₂ i hi)
  have hj :=
    (ReportingHostRelocation.meets
          (LightWantedJoin.program_meets (d := d + 1) (μ := μ₃) (keys := lc) (offsets := off) (flat := flat) (NR := NR)
            (M := M) (dst := dst) (n := NL) lkey rkey hrkey hw (by omega) (by omega) (by omega) hpairSpace (by omega)
            hlkey hleft₃ H)
          bucketProgram).append
      [body 0 2 9]
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
    | refine _root_.Light.Ends.callToThen (hj _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hj ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lkey, rkey, code]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [lkey, rkey, code] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lkey, rkey, code] <;> omega)
    on_goal -1 =>
      (rintro matchCount μ₄ ⟨hmatch, hpairs, hkeepJ⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmatchTotal : matchCount = (total M left right NL NR shift : ℤ) := hmatch
  have htwoWord : (2 * (total M left right NL NR shift : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 2 * total M left right NL NR shift ≤ lim.space by omega) :
          (2 * (total M left right NL NR shift : ℤ)) ≤ lim.space).trans
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
    refine _root_.Light.Ends.storeToThen free (total M left right NL NR shift : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmatchTotal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmatchTotal] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmatchTotal] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 1) (dst : ℕ) ?_ ?_ ?_
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
    refine _root_.Light.Ends.storeToThen (free + 2) (dst + 2 * total M left right NL NR shift : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmatchTotal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmatchTotal] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmatchTotal] <;> omega)
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
    refine _root_.Light.Ends.storeToThen (free + 3) shift ?_ ?_ ?_
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
    refine _root_.Light.Ends.setToThen (free : ℕ) ?_ ?_ ?_
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
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, WantedPairs.pairs μ₃ off flat lkey NL, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [dst]
    · simp [dst]
    · simp
    · exact WantedPairs.pairs_length H NL hlkey
    · exact WantedPairs.pairs_nodup H hlkey hrkey
    · intro i j
      rw [WantedPairs.mem_pairs H hlkey hrkey]
      simp only [lkey, rkey, code_eq_iff hM]
    · intro i hi
      change
        Function.update (Function.update (Function.update (Function.update μ₄ free _) (free + 1) _) (free + 2) _)
            (free + 3) _ (dst + i) =
          _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hpairs i hi
  · intro i hi
    change
      Function.update (Function.update (Function.update (Function.update μ₄ free _) (free + 1) _) (free + 2) _)
          (free + 3) _ i =
        μ i
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    rw [hkeepJ _ (by omega), hkeepB _ (by omega), hkeepR _ ⟨by omega, Or.inl (by omega)⟩,
      hkeepL _ ⟨by omega, Or.inl (by omega)⟩]
end ThreeSum.LightWantedSetup
