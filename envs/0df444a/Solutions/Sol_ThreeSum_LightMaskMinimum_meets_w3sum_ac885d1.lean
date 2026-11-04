-- Prove2me | solution 1 for ThreeSum.LightMaskMinimum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:09.68339+00:00
-- url     : https://prove2.me/submissions/12ab82ef-ffaa-4503-9def-1f810f74e9e0

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_lt_iff
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskMinimum
theorem _root_.solution {pMain pPowers pErase : ℕ} (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody) (hErase : P[pErase]? = some (LightMaskErase.body pErase)) {μ : ℕ → ℤ}
    {L work d : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work + (L + 1) ≤ lim.space) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [L, subsetMask S, work] μ (time L) (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) :=
  by
  have hmin : (S.min' hS).val < L := (S.min' hS).isLt
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := L + 1) (b := 2) hPowers hw hspace
      (by
        intro i hi
        have hh : (2 ^ i : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) hi
        exact (by exact_mod_cast hh : ((2 ^ i : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hword)
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
    refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := L * (LightMaskErase.time L + 80) + 20) (Q := Inv μ₁ S hS work powRet L) (Inv μ₁ S hS work powRet)
        L (LightMaskErase.time L + 60) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, ?_⟩
    simp [Inv, best, update_frame_setLocal]
    change
      frame [(L : ℤ), subsetMask S, work, powRet, L, 0] = frame ([(L : ℤ), subsetMask S, work, powRet, L, 0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r, rfl⟩
    have hb : best S hS j ≤ L := by unfold best; split <;> omega
    have hc :=
      LightMaskErase.meets hErase μ₁ hw hspace hword hpowers L j (subsetMask S) le_rfl (Nat.le_of_lt hj)
        (subsetMask_isMask S).1 (d + 1) (by omega)
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
        _root_.Light.Ends.iteIffThen ((eraseMask L j (subsetMask S) : ℤ) < (subsetMask S : ℤ)) (fun hbit => ?_)
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
    · have ha : (⟨j, hj⟩ : Fin L) ∈ S := (eraseMask_lt_iff S ⟨j, hj⟩).mp (by exact_mod_cast hbit)
      have hminle : (S.min' hS).val ≤ j := Finset.min'_le S ⟨j, hj⟩ ha
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((j : ℤ) < (best S hS j : ℤ)) (fun hless => ?_) (fun hnless => ?_) ?_ ?_
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
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have hbestgt : j < best S hS j := by exact_mod_cast hless
        have heq : (S.min' hS).val = j := by
          unfold best at hbestgt
          split at hbestgt <;> omega
        have hnext : best S hS (j + 1) = j := by simp [best, heq]
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (j : ℕ) ?_ ?_ ?_
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
        refine ⟨by simp, erased, ?_⟩
        simp [Inv, update_frame_setLocal, hnext]
      · have hbestle : best S hS j ≤ j :=
          by
          have hh : ¬j < best S hS j := by exact_mod_cast hnless
          omega
        have hlt : (S.min' hS).val < j := by
          unfold best at hbestle
          split at hbestle <;> omega
        have heq : best S hS j = best S hS (j + 1) := by simp [best, hlt, show (S.min' hS).val < j + 1 by omega]
        apply Ends.skip
        refine ⟨by simp, erased, ?_⟩
        simp [Inv, update_frame_setLocal, heq]
    · have ha : (⟨j, hj⟩ : Fin L) ∉ S := by
        intro hh
        exact hnbit (by exact_mod_cast (eraseMask_lt_iff S ⟨j, hj⟩).mpr hh)
      have hne : (S.min' hS).val ≠ j := by
        intro hh
        have he : S.min' hS = (⟨j, hj⟩ : Fin L) := Fin.ext hh
        exact ha (he ▸ Finset.min'_mem S hS)
      have heq : best S hS j = best S hS (j + 1) := by
        unfold best
        have hh : (S.min' hS).val < j ↔ (S.min' hS).val < j + 1 := by omega
        simp only [hh]
      apply Ends.skip
      refine ⟨by simp, erased, ?_⟩
      simp [Inv, update_frame_setLocal, heq]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨r, rfl⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen ((S.min' hS).val : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, best, hmin]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [best, hmin] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, best, hmin] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, fun i hi => hkept i (Or.inl hi)⟩
end ThreeSum.LightMaskMinimum
