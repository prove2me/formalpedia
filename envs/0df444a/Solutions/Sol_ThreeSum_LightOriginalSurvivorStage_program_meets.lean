-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorStage.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:42.292116+00:00
-- url     : https://prove2.me/submissions/a0815029-7769-4ef8-a634-2ca050433686

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_lengths
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_partition_lengths
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Theorems.Thm_ThreeSum_LightReportingGather_meets
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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorStage
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightOriginalSurvivorStage
theorem _root_.solution
    {keyBase n hist q out valuesBase scanBase scanN targetBase targetN powers W L U d dstValues dstKeys lengthCell : ℕ}
    (sign : ℤ) (μ : ℕ → ℤ) (keys : ℕ → ℕ) (values scan target : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeysSpace : keyBase + n ≤ out) (hhistSpace : hist + q ≤ out) (hvaluesSpace : valuesBase + n ≤ out)
    (hscanSpace : scanBase + scanN ≤ out) (htargetSpace : targetBase + targetN ≤ out) (hspace : powers + (W + 1) ≤ out)
    (hfirst : out + 2 * n ≤ dstValues) (hsecond : dstValues + n ≤ dstKeys) (hthird : dstKeys + n ≤ lengthCell)
    (hlast : lengthCell + 1 ≤ lim.space) (hword : ((targetN + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hkeys : ∀ i < n, keys i < q) (hreadKeys : ∀ i < n, μ (keyBase + i) = (keys i : ℤ))
    (hcounts : ∀ k < q, μ (hist + k) = (counts keys n k : ℤ)) (hvalues : ∀ i < n, |values i| ≤ U)
    (hreadValues : ∀ i < n, μ (valuesBase + i) = values i) (hscan : ∀ i < scanN, |scan i| ≤ U)
    (hreadScan : ∀ i < scanN, μ (scanBase + i) = scan i) (hreadTarget : ∀ i < targetN, μ (targetBase + i) = target i)
    (hsign : |sign| ≤ 1) (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < targetN → target i < target j) (hL : L ≤ W) (htargetN : targetN < 2 ^ L)
    (hd : d + L + 4 ≤ lim.depth) :
    Meets lim program 7 d
      [keyBase, n, hist, q, out, valuesBase, scanBase, scanN, targetBase, targetN, powers, L, sign, dstValues, dstKeys,
        lengthCell]
      μ (time keys n scanN L)
      (fun ret ν =>
        ret =
            (LightDeletedTwoSum.flag (badIndex keys n) values scan target targetN scanN (badIndices keys n).length
                sign :
              ℤ) ∧
          ν lengthCell = ((indices keys n).length : ℤ) ∧
            Seg ν out (cells (indices keys n)) ∧
              (∀ i < (indices keys n).length, ν (dstValues + i) = values (index keys n i)) ∧
                (∀ i < (indices keys n).length, ν (dstKeys + i) = (keys (index keys n i) : ℤ)) ∧
                  Kept μ ν out ∧
                    Above μ ν lengthCell ∧ Preserves μ ν out n dstValues dstKeys (indices keys n).length lengthCell) :=
  by
  have ht := length_le keys n
  have hb := (lengths keys (counts keys n) n).2
  have hpartition := partition_lengths keys (counts keys n) n
  have hpart : (indices keys n).length + (badIndices keys n).length = n := hpartition
  have hnword : (n : ℤ) ≤ lim.word := by omega
  have hcword : ∀ k < q, (counts keys n k : ℤ) ≤ lim.word :=
    by
    intro k hk
    exact (Int.ofNat_le.mpr (LightHistogram.count_le keys k n)).trans hnword
  have hf :=
    LightOriginalBucketFilter.meets (P := program) (d := d + 1) (pMain := 1) (by rfl) μ keys (counts keys n) hw
      hkeysSpace hhistSpace (by omega) hkeys hreadKeys hcounts hcword (by omega)
  apply Meets.of_body (p := 7) (by rfl : program[7]? = some body)
  unfold body time LightOriginalCollisionCleanup.time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalBucketFilter.time, LightDeletedTwoSum.time, LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time] <;>
          omega)
    on_goal -1 => (rintro badN ν ⟨hBadN, hGood, hBad, H⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  change badN = ((badIndices keys n).length : ℤ) at hBadN
  have hKeep {x : ℕ} (hx : x < out) : ν x = μ x := H x (Or.inl hx)
  have hIdRead : ∀ i < (badIndices keys n).length, ν (out + n + i) = (badIndex keys n i : ℤ) :=
    by
    intro i hi
    have hh := hBad i (by simpa [cells, badIndices] using hi)
    rw [badIndex, dif_pos hi]
    simpa [cells, List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.getElem_map, badIndices] using hh
  have hPowers : Powers ν powers W := by
    intro i hi
    rw [hKeep (by omega), hpowers i hi]
  have hc :=
    LightDeletedTwoSum.meets (P := program) (d := d + 1) (badBase := out + n) (badN := (badIndices keys n).length)
      (valuesBase := valuesBase) (originalN := n) (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase)
      (targetN := targetN) (powers := powers) (W := W) (L := L) (U := U) sign (pMain := 2) (pTwoSum := 3) (pLookup := 4)
      (pSearch := 5) rfl rfl rfl rfl ν (badIndex keys n) values scan target hw (by omega) (by omega) (by omega)
      (by omega) (by omega) hword (fun i hi => badIndex_lt hi) hIdRead hvalues
      (fun i hi => by rw [hKeep (by omega), hreadValues i hi]) hscan
      (fun i hi => by rw [hKeep (by omega), hreadScan i hi]) (fun i hi => by rw [hKeep (by omega), hreadTarget i hi])
      hsign hvalueWord hPowers hsorted hL htargetN (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hBadN, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hBadN, LightOriginalBucketFilter.time, LightDeletedTwoSum.time, LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hBadN, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time] <;>
          omega)
    on_goal -1 => (rintro result ξ ⟨hResult, hMem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ξ
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen ((indices keys n).length : ℤ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hBadN, Int.natCast_add]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hBadN, Int.natCast_add] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hBadN, Int.natCast_add] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hGoodRead : ∀ i < (indices keys n).length, ν (out + i) = (index keys n i : ℤ) :=
    by
    intro i hi
    have hh := hGood i (by simpa [cells, indices] using hi)
    rw [index, dif_pos hi]
    simpa [cells, indices, List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.getElem_map] using hh
  have hv :=
    LightReportingGather.meets (P := program) (p := 6) (d := d + 1) (indices := out) (src := valuesBase) (dst :=
      dstValues) (t := (indices keys n).length) (n := n) rfl (index keys n) values hw (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (fun i hi => index_lt hi) hGoodRead
      (fun i hi => by rw [hKeep (by omega), hreadValues i hi]) (fun i hi => (hvalues i hi).trans (by omega))
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hv _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hv ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalBucketFilter.time, LightDeletedTwoSum.time, LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time] <;>
          omega)
    on_goal -1 => (rintro ignored ξ ⟨hValues, Hv⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hGoodRead' : ∀ i < (indices keys n).length, ξ (out + i) = (index keys n i : ℤ) :=
    by
    intro i hi
    exact (Hv _ (Or.inl (by omega))).trans (hGoodRead i hi)
  have hk :=
    LightReportingGather.meets (P := program) (p := 6) (d := d + 1) (indices := out) (src := keyBase) (dst := dstKeys)
      (t := (indices keys n).length) (n := n) rfl (index keys n) (fun i => (keys i : ℤ)) hw (by omega) (by omega)
      (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (fun i hi => index_lt hi) hGoodRead'
      (fun i hi => by rw [Hv _ (Or.inl (by omega)), hKeep (by omega), hreadKeys i hi])
      (fun i hi => by rw [abs_of_nonneg (Int.natCast_nonneg _)]; have hh := hkeys i hi; omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hk ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalBucketFilter.time, LightDeletedTwoSum.time, LightReportingGather.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time, LightReportingGather.time] <;>
          omega)
    on_goal -1 => (rintro ignored₂ ζ ⟨hKeys, Hk⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen lengthCell ((indices keys n).length : ℤ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
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
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen result ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hResult]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hResult] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hResult] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hResult
  · simp
  · intro i hi
    have hi' : i < (indices keys n).length := by simpa [cells] using hi
    simpa [indices] using
      (show (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (out + i) = (cells (indices keys n))[i] from
        by
        rw [Function.update_of_ne (by omega), Hk _ (Or.inl (by omega)), Hv _ (Or.inl (by omega))]
        exact hGood i hi)
  · intro i hi
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (dstValues + i) = _
    rw [Function.update_of_ne (by omega), Hk _ (Or.inl (by omega))]
    exact hValues i hi
  · intro i hi
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (dstKeys + i) = _
    rw [Function.update_of_ne (by omega)]
    exact hKeys i hi
  · intro x hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne (by omega), Hk _ (Or.inl (by omega)), Hv _ (Or.inl (by omega))]
    exact hKeep hx
  · intro x hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne (by omega), Hk _ (Or.inr (by omega)), Hv _ (Or.inr (by omega))]
    exact H x (Or.inr (by omega))
  · intro x hx
    obtain ⟨hf, hv, hk, hne⟩ := hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne hne, Hk x hk, Hv x hv]
    exact H x hf
end ThreeSum.LightOriginalSurvivorStage
