-- Prove2me | solution 1 for ThreeSum.LightRawAKeys.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:55.516733+00:00
-- url     : https://prove2.me/submissions/238f483e-38b6-47b6-8d2a-edf7efa86b58

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidues_residue_cast
import Theorems.Thm_ThreeSum_LightResidues_residues_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_c96b4d5a282bcbcf
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Definitions.Def_WeightedCache3SUM_Alias_c7e36c2f93ed268d
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRawAKeys
theorem _root_.solution {pMain pResidues pAffine pEmod src free p U : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pResidues pAffine)) (hres : P[pResidues]? = some (residuesBody pEmod))
    (haff : P[pAffine]? = some LightReportingAffine.body) (hem : P[pEmod]? = some emodBody) (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hsrc : src + xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space) (hword : (word p U : ℤ) ≤ lim.word) (hd : d + 2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, xs.length, p, free] μ (time xs.length U)
      (fun r ν => r = (free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) :=
  by
  let n := xs.length
  let work := free + 3 * n
  have hs : free + 3 * n + Nat.log 2 (U + 1) + 2 ≤ lim.space := hspace
  have hew : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word := by
    simpa only [word, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hword
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpw : 2 * (p : ℤ) ≤ lim.word := by omega
  have horiginal (i : ℕ) (hi : i < n) : μ (src + i) = xs.getD i 0 :=
    by
    rw [List.getD_eq_getElem _ _ hi]
    exact hread i hi
  have hremNonneg (i : ℕ) : (0 : ℤ) ≤ xs.getD i 0 % (p : ℤ) := Int.emod_nonneg _ hpz.ne'
  have hremLt (i : ℕ) : xs.getD i 0 % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ hpz
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen (work : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, work, n, LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [work, n, LightReportingAffine.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, work, n, LightReportingAffine.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hr :=
    residues_meets (d := d + 1) (μ := μ) (src := src) (dst := free + n) (work := work) (n := n) (p := p) (U := U) (c :=
      1) hres hem hw (by omega) hp (by dsimp [work]; omega) (by dsimp [work]; omega) (by dsimp [work]; omega)
      (by left; omega) (by norm_num) hew
      (fun i hi => by rw [horiginal i hi, List.getD_eq_getElem _ _ hi]; exact hvalues _ (List.getElem_mem hi))
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, n, LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [n, LightReportingAffine.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, n, LightReportingAffine.time] <;> omega)
    on_goal -1 => (rintro vr μ₁ ⟨hresValues, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmid (i : ℕ) (hi : i < n) : μ₁ (free + n + i) = xs.getD i 0 % (p : ℤ) := by
    rw [hresValues i hi, residue_cast hp, one_mul, horiginal i hi]
  have hl :=
    LightReportingAffine.meets (d := d + 1) (μ := μ₁) (src := free + n) (dst := free) (n := n) (b := -(p : ℤ)) (c := 1)
      haff hw (by omega) (by omega) (by right; right; omega)
      (fun i hi => by rw [one_mul, hmid i hi, abs_of_nonneg (hremNonneg i)]; have hh := hremLt i; omega)
      (fun i hi => by
        rw [one_mul, hmid i hi]; apply abs_le.mpr; have h0 := hremNonneg i; have h1 := hremLt i
        constructor <;> omega)
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, n, LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [n, LightReportingAffine.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, n, LightReportingAffine.time] <;> omega)
    on_goal -1 => (rintro vl μ₂ ⟨hleft, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hmid₂ (i : ℕ) (hi : i < n) : μ₂ (free + n + i) = xs.getD i 0 % (p : ℤ) := by
    rw [hkeep₂ _ (Or.inr (by omega)), hmid i hi]
  have hr :=
    LightReportingAffine.meets (d := d + 1) (μ := μ₂) (src := free + n) (dst := free + 2 * n) (n := n) (b := (p : ℤ))
      (c := 1) haff hw (by omega) (by omega) (by right; left; omega)
      (fun i hi => by rw [one_mul, hmid₂ i hi, abs_of_nonneg (hremNonneg i)]; have hh := hremLt i; omega)
      (fun i hi => by
        rw [one_mul, hmid₂ i hi]; apply abs_le.mpr; have h0 := hremNonneg i; have h1 := hremLt i
        constructor <;> omega)
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, n, LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [n, LightReportingAffine.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, n, LightReportingAffine.time] <;> omega)
    on_goal -1 => (rintro vp μ₃ ⟨hright, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, n, LightReportingAffine.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [n, LightReportingAffine.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, n, LightReportingAffine.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · rw [keys_eq_liftRows]
    apply LocalKeyArraySemantics.seg_flatMap_rows _ _ n free (fun j hj => by simp only [List.length_map]; rfl)
    intro j hj i hi
    have hj3 : j < 3 := by simpa only [List.length_finRange] using hj
    rw [List.getElem_map]
    have hget : xs[i] = xs.getD i 0 := (List.getD_eq_getElem _ _ hi).symm
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [Nat.zero_mul, Nat.add_zero]
      change μ₃ (free + i) = xs[i] % (p : ℤ) + lift (0 : Fin 3) * (p : ℤ)
      rw [hget, show lift (0 : Fin 3) = -1 from rfl, neg_one_mul]
      rw [hkeep₃ _ (Or.inl (by omega)), hleft i hi, one_mul, hmid i hi]
      omega
    · simp only [Nat.one_mul]
      change μ₃ (free + n + i) = xs[i] % (p : ℤ) + lift (1 : Fin 3) * (p : ℤ)
      rw [hget, show lift (1 : Fin 3) = 0 from rfl, zero_mul, add_zero]
      rw [hkeep₃ _ (Or.inl (by omega)), hmid₂ i hi]
    · change μ₃ (free + 2 * n + i) = xs[i] % (p : ℤ) + lift (2 : Fin 3) * (p : ℤ)
      rw [hget, show lift (2 : Fin 3) = 1 from rfl, one_mul, hright i hi, one_mul, hmid₂ i hi]
      omega
  · intro a ha
    change μ₃ a = μ a
    rw [hkeep₃ _ (Or.inl (by omega)), hkeep₂ _ (Or.inl ha), hkeep₁ _ ⟨by dsimp [work]; omega, Or.inl (by omega)⟩]
end ThreeSum.LightRawAKeys
