-- Prove2me | solution 1 for ThreeSum.LightGlobalKeys.Procs.meets_with_masks_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:29.804507+00:00
-- url     : https://prove2.me/submissions/b17cad9f-189a-4113-a804-d93f081b1d4d

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Theorems.Thm_ThreeSum_LightGlobalKeys_localCount_pos
import Theorems.Thm_ThreeSum_LightGlobalKeys_localKeys_length
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
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_localKeys_bounded
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LocalKeyArraySemantics_meets_original
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
namespace ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
private theorem sum_parts (a b c j : ℕ) :
    a ≤ a + b + c + j + 512 ∧ b ≤ a + b + c + j + 512 ∧ c ≤ a + b + c + j + 512 ∧ j ≤ a + b + c + j + 512 := by omega
private theorem word_parts (h J : ℕ) :
    2 ^ (512 * h + 1) ≤ word h J ∧
      LightLocalKeys.word (512 * h) (localPrime h) (scheduleSize h) ≤ word h J ∧
        LightRadixKeys.word (localPrime h) (512 * h * localPrime h) J ≤ word h J ∧ J ≤ word h J :=
  sum_parts _ _ _ _
private theorem int_mul_le_word {a b c : ℕ} {w : ℤ} (hab : a * b ≤ c) (hc : (c : ℤ) ≤ w) : (a : ℤ) * (b : ℤ) ≤ w := by
  exact (show (a : ℤ) * (b : ℤ) ≤ (c : ℤ) by simpa only [Nat.cast_mul] using Int.ofNat_le.mpr hab).trans hc
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightGlobalKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalKeys
namespace Procs
theorem _root_.solution {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + J + 5 ≤ lim.depth) (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps + scheduleSize h * (2 * (512 * h)) ≤ free)
    (hreadFalse :
      ∀ j < scheduleSize h,
        ∀ i < 512 * h, μ (maps + j * (2 * (512 * h)) + i) = (BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue :
      ∀ j < scheduleSize h,
        ∀ i < 512 * h, μ (maps + j * (2 * (512 * h)) + 512 * h + i) = (BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512 * h, 2 * h, scheduleSize h, localPrime h, J, maps, outputCount (512 * h) h, free] μ
      (time h J)
      (fun r ν =>
        r = ((scratch free h + LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
          ν (scratch free h + LightRadixKeys.offset (localCount h) J) = ((localCount h ^ J : ℕ) : ℤ) ∧
            Seg ν (scratch free h + LightRadixKeys.offset (localCount h) J + 1) (globalKeys h J) ∧
              (∀ i < outputCount (512 * h) h, ν (free + i) = (LocalMaskGraph.maskAt (512 * h) (2 * h) i : ℤ)) ∧
                Kept μ ν free) :=
  by
  let n := outputCount (512 * h) h
  let m := localCount h
  let dst := free + n
  let work := scratch free h
  have hwork : work = dst + m := rfl
  have hlspace : LightLocalKeyRow.space work (512 * h) n ≤ lim.space := (le_max_left _ _).trans hspace
  have hgspace : LightRadixKeys.space work m J ≤ lim.space := (le_max_right _ _).trans hspace
  have hs : work + 512 * h + 2 * n + (512 * h + 1) ≤ lim.space := hlspace
  have hbudget (x : ℕ) (hx : x ≤ word h J) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hpword := hbudget (2 ^ (512 * h + 1)) (word_parts h J).1
  have hlword := hbudget (LightLocalKeys.word (512 * h) (localPrime h) (scheduleSize h)) (word_parts h J).2.1
  have hgword := hbudget (LightRadixKeys.word (localPrime h) (512 * h * localPrime h) J) (word_parts h J).2.2.1
  have hJword := hbudget J (word_parts h J).2.2.2
  have hcount := localCount_pos h
  have hlen : (localKeys h).length = m := localKeys_length h
  have hprodWord : (scheduleSize h : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have hh : scheduleSize h * n ≤ lim.space := by change m ≤ lim.space; omega
    exact int_mul_le_word hh hw
  have hprodNonneg : (0 : ℤ) ≤ (scheduleSize h : ℤ) * (n : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hprodWord' : (scheduleSize h : ℤ) * (outputCount (512 * h) h : ℤ) ≤ lim.word := hprodWord
  have hprodNonneg' : (0 : ℤ) ≤ (scheduleSize h : ℤ) * (outputCount (512 * h) h : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hproduct : (scheduleSize h : ℤ) * (outputCount (512 * h) h : ℤ) = (m : ℤ) := by
    simp only [m, localCount, Nat.cast_mul]
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
    refine _root_.Light.Ends.setToThen (scheduleSize h * outputCount (512 * h) h : ℕ) ?_ ?_ ?_
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
    refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dst, n]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [dst, n] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dst, n] <;> omega)
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
    refine _root_.Light.Ends.setToThen (work : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hwork, hproduct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hwork, hproduct] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hwork, hproduct] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have he :=
    LightSubsetEnumerationSetup.meets (d := d + 1) (μ := μ) (L := 512 * h) (k := 2 * h) (dst := free) (work := work)
      S.enum S.powers S.layer hw (by omega) hpword (by omega) (by change free + n ≤ work; dsimp [dst] at hwork; omega)
      (by omega)
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
    | refine _root_.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen he ?_ ?_ ?_ ?_
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
      (rintro count μ₁ ⟨hcountVal, hmasks, hpowers, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hc : count = (n : ℤ) := hcountVal
  have hmRead (i : ℕ) (hi : i < n) : μ₁ (free + i) = (LocalMaskGraph.maskAt (512 * h) (2 * h) i : ℤ) :=
    by
    have hi' : i < (enumerateLayer (512 * h) (2 * h)).length :=
      by
      rw [enumerateLayer_length]
      exact hi
    have he := hmasks i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt, List.getD_eq_getElem _ _ hi', List.getElem_map] using he
  have hfi (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512 * h) :
    μ₁ (maps + j * (2 * (512 * h)) + i) = (BlockCoefficientRows.mapRow h false j i : ℤ) :=
    by
    have hh := Nat.mul_le_mul_right (2 * (512 * h)) (show j + 1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul, one_mul] at hh
    rw [hkeep₁ _ ⟨by omega, Or.inl (by omega)⟩]
    exact hreadFalse j hj i hi
  have hti (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512 * h) :
    μ₁ (maps + j * (2 * (512 * h)) + 512 * h + i) = (BlockCoefficientRows.mapRow h true j i : ℤ) :=
    by
    have hh := Nat.mul_le_mul_right (2 * (512 * h)) (show j + 1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul, one_mul] at hh
    rw [hkeep₁ _ ⟨by omega, Or.inl (by omega)⟩]
    exact hreadTrue j hj i hi
  have hl :=
    LocalKeyArraySemantics.meets_original (d := d + 1) (μ := μ₁) (h := h) (masks := free) (maps := maps) (dst := dst)
      (free := work) S.locals hw (by omega) hlspace le_rfl (by dsimp [dst]; omega)
      (by dsimp [localCount, m] at *; omega) hlword hmRead hfi hti
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hc] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc] <;> omega)
    on_goal -1 => (rintro result μ₂ ⟨hkeys, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hg :=
    LightRadixKeys.meets (src := dst) (dst := work) (p := localPrime h) (U := 512 * h * localPrime h) S.globalProc
      S.rows S.affine (localKeys h) hw (by rw [hlen]; omega) (by rw [hlen]; exact hcount) (localKeys_bounded h) J
      (d + 1) μ₂ (by simpa only [hlen] using hgspace) hgword (by omega) hkeys
  simp only [hlen] at hg
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
    | refine _root_.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, m]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [m] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, m] <;> omega)
    on_goal -1 =>
      (rintro final μ₃ ⟨hresult, hheader, hglobal, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hresult, hheader, hglobal, ?_, ?_⟩
  · intro i hi
    change μ₃ (free + i) = (LocalMaskGraph.maskAt (512 * h) (2 * h) i : ℤ)
    rw [hkeep₃ _ (by dsimp [dst] at hwork; change i < n at hi; omega),
      hkeep₂ _ (by dsimp [dst]; change i < n at hi; omega)]
    exact hmRead i hi
  · intro a ha
    change μ₃ a = μ a
    rw [hkeep₃ _ (by omega), hkeep₂ _ (by dsimp [dst]; omega), hkeep₁ _ ⟨by omega, Or.inl ha⟩]
end Procs
end ThreeSum.LightGlobalKeys
