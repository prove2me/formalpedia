-- Prove2me | solution 1 for ThreeSum.LightQueryWeights.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:42.956799+00:00
-- url     : https://prove2.me/submissions/b6e6f88b-a012-4134-987e-94ebac5f653b

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_lt_iff
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length_le
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_succ
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_succ
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.missingSets_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryWeights
theorem _root_.solution {pMain pPowers pErase : ℕ} (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody) (hErase : P[pErase]? = some (LightMaskErase.body pErase)) {μ : ℕ → ℤ}
    {W dst work d : ℕ} (Q : Finset (Fin W)) (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + W ≤ work)
    (hspace : work + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + W + 1 ≤ lim.depth) :
    Meets lim P pMain d [W, subsetMask Q, dst, work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧ SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧ KeptBut μ μ' work dst W) :=
  by
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := W + 1) (b := 2) hPowers hw hspace
      (by
        intro i hi
        have hh : (2 ^ i : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) hi
        exact (by exact_mod_cast hh : ((2 ^ i : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightMaskErase.time] <;> omega)
    on_goal -1 => (rintro powRet μ₁ ⟨hpow, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowers := powers_of_segment hpow
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightMaskErase.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightMaskErase.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightMaskErase.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := W * (LightMaskErase.time W + 80) + 20) (Q := Inv μ Q dst work powRet W) (Inv μ Q dst work powRet)
        W (LightMaskErase.time W + 60) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, μ₁, ?_, by simp [SegN], hpowers, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(W : ℤ), subsetMask Q, dst, work, powRet, 0, 0] =
          frame ([(W : ℤ), subsetMask Q, dst, work, powRet, 0, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      exact hkept i (Or.inl hi.1)
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hseg, hpowers', hkeep⟩
    have hcBound := positions_length_le Q j
    have hc :=
      LightMaskErase.meets hErase μ' hw hspace hword hpowers' W j (subsetMask Q) le_rfl (Nat.le_of_lt hj)
        (subsetMask_isMask Q).1 (d + 1) (by omega)
    unfold roundBody
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
      on_goal -1 => (rintro erased μ₂ ⟨herased, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine
        _root_.Light.Ends.iteIffThen ((eraseMask W j (subsetMask Q) : ℤ) < (subsetMask Q : ℤ)) (fun hbit => ?_)
          (fun hnbit => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, herased,
              LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [herased, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, herased, LightMaskErase.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have ha : (⟨j, hj⟩ : Fin W) ∈ Q := (eraseMask_lt_iff Q ⟨j, hj⟩).mp (by exact_mod_cast hbit)
      have hnat : j ∈ natPositions Q := Finset.mem_map.mpr ⟨⟨j, hj⟩, ha, rfl⟩
      have hnext := selectedPowers_succ Q j
      rw [if_pos hnat] at hnext
      have hlen : (positions Q (j + 1)).length = (positions Q j).length + 1 :=
        by
        rw [positions_succ, if_pos hnat]
        simp
      have hread := hpowers' j (Nat.le_of_lt hj)
      have hvalWord : ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
        by
        have hh : (2 ^ j : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact (by exact_mod_cast hh : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen (dst + (positions Q j).length) (2 ^ j : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightMaskErase.time, hread]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightMaskErase.time, hread] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time, hread] <;> omega)
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
        refine _root_.Light.Ends.setToThen ((positions Q j).length + 1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskErase.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, erased, Function.update μ' (dst + (positions Q j).length) ((2 ^ j : ℕ) : ℤ), ?_, ?_, ?_, ?_⟩
      · simp [update_frame_setLocal, hlen]
      · rw [hnext]
        simpa only [selectedPowers_length] using SegN.snoc hseg (2 ^ j)
      · intro i hi
        change Function.update μ' (dst + (positions Q j).length) ((2 ^ j : ℕ) : ℤ) (work + i) = _
        rw [Function.update_of_ne (by omega)]
        exact hpowers' i hi
      · intro i hi
        change Function.update μ' (dst + (positions Q j).length) ((2 ^ j : ℕ) : ℤ) i = _
        rw [Function.update_of_ne (by omega)]
        exact hkeep i hi
    · have ha : (⟨j, hj⟩ : Fin W) ∉ Q := by
        intro hh
        exact hnbit (by exact_mod_cast (eraseMask_lt_iff Q ⟨j, hj⟩).mpr hh)
      have hnat : j ∉ natPositions Q := by
        intro hh
        obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp hh
        exact ha ((Fin.ext hij : i = ⟨j, hj⟩) ▸ hi)
      have hpos : positions Q (j + 1) = positions Q j := by rw [positions_succ, if_neg hnat, List.append_nil]
      have hnext : selectedPowers Q (j + 1) = selectedPowers Q j := by
        rw [selectedPowers_succ, if_neg hnat, List.append_nil]
      apply Ends.skip
      refine ⟨by simp, erased, μ', ?_, ?_, hpowers', hkeep⟩
      · simp [update_frame_setLocal, hpos]
      · rwa [hnext]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, hseg, hpowers', hkeep⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨r, μ', rfl, hseg, hpowers', hkeep⟩
    have hc := positions_length_le Q W
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (Q.card : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, positions_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [positions_length] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, positions_length] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hseg, hpowers', hkeep⟩
end ThreeSum.LightQueryWeights
