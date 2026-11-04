-- Prove2me | solution 1 for ThreeSum.LightMaskUnion.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:10.751569+00:00
-- url     : https://prove2.me/submissions/7d84c993-16ab-41cb-93aa-38906e1f5ac5

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_LocalsBut_update
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
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_lt_iff
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_card_succ_new
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_mask_succ_new
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_already
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_notMem
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.MaskUnion.scanSet_all
attribute [local simp] ThreeSum.MaskUnion.scanSet_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskUnion
theorem _root_.solution {pMain pPowers pErase : ℕ} (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody) (hErase : P[pErase]? = some (LightMaskErase.body pErase)) {μ : ℕ → ℤ}
    {W dst work d : ℕ} (A B : Finset (Fin W)) (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + 1 ≤ work)
    (hspace : work + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + W + 1 ≤ lim.depth) :
    Meets lim P pMain d [W, A.card, subsetMask A, subsetMask B, dst, work] μ (time W)
      (fun r μ' =>
        r = (subsetMask (A ∪ B) : ℤ) ∧ μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧ KeptBut μ μ' work dst 1) :=
  by
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hcard (S : Finset (Fin W)) : S.card ≤ W := by simpa using Finset.card_le_univ S
  have hmask (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word :=
    by
    have hn :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_succ W))
    exact (by exact_mod_cast hn : (subsetMask S : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hAcard := hcard A
  have hAmask := hmask A
  have hBmask := hmask B
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
    refine _root_.Light.Ends.setToThen (A.card : ℕ) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (subsetMask A : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := W * (2 * LightMaskErase.time W + 160) + 20) (Q := Inv μ₁ A B dst work powRet W)
        (Inv μ₁ A B dst work powRet) W (2 * LightMaskErase.time W + 140) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, 0, ?_⟩
    simp [update_frame_setLocal]
    change
      frame [(W : ℤ), A.card, subsetMask A, subsetMask B, dst, work, powRet, A.card, subsetMask A, 0] =
        frame ([(W : ℤ), A.card, subsetMask A, subsetMask B, dst, work, powRet, A.card, subsetMask A, 0] ++ [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨eB, eA, rfl⟩
    have hcurrentCard := hcard (scanSet A B j)
    have hcurrentMask := hmask (scanSet A B j)
    have hnextCard := hcard (scanSet A B (j + 1))
    have hnextMask := hmask (scanSet A B (j + 1))
    have hcB :=
      LightMaskErase.meets hErase μ₁ hw hspace hword hpowers W j (subsetMask B) le_rfl (Nat.le_of_lt hj)
        (subsetMask_isMask B).1 (d + 1) (by omega)
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
      | refine _root_.Light.Ends.callToThen (hcB _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcB ?_ ?_ ?_ ?_
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
      on_goal -1 => (rintro erasedB μ₂ ⟨herasedB, hmemB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    have hcA :=
      LightMaskErase.meets hErase μ₁ hw hspace hword hpowers W j (subsetMask A) le_rfl (Nat.le_of_lt hj)
        (subsetMask_isMask A).1 (d + 1) (by omega)
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
      | refine _root_.Light.Ends.callToThen (hcA _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcA ?_ ?_ ?_ ?_
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
      on_goal -1 => (rintro erasedA μ₂ ⟨herasedA, hmemA⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
        _root_.Light.Ends.iteIffThen ((eraseMask W j (subsetMask B) : ℤ) < (subsetMask B : ℤ)) (fun hbitB => ?_)
          (fun hnbitB => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, herasedB,
              LightMaskErase.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [herasedB, LightMaskErase.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, herasedB, LightMaskErase.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hb : (⟨j, hj⟩ : Fin W) ∈ B := (eraseMask_lt_iff B ⟨j, hj⟩).mp (by exact_mod_cast hbitB)
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
          _root_.Light.Ends.iteIffThen ((eraseMask W j (subsetMask A) : ℤ) < (subsetMask A : ℤ)) (fun hbitA => ?_)
            (fun hnbitA => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, herasedA,
                LightMaskErase.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [herasedA, LightMaskErase.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, herasedA, LightMaskErase.time] <;> omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have ha : (⟨j, hj⟩ : Fin W) ∈ A := (eraseMask_lt_iff A ⟨j, hj⟩).mp (by exact_mod_cast hbitA)
        have he := scanSet_succ_already A B hj hb ha
        apply Ends.skip
        exact ⟨by simp, erasedB, erasedA, by simp [update_frame_setLocal, he]⟩
      · have ha : (⟨j, hj⟩ : Fin W) ∉ A := by
          intro hh
          exact hnbitA (by exact_mod_cast (eraseMask_lt_iff A ⟨j, hj⟩).mpr hh)
        have hc := scanSet_card_succ_new A B hj hb ha
        have hm := scanSet_mask_succ_new A B hj hb ha
        have hread := hpowers j (Nat.le_of_lt hj)
        have hsum : (subsetMask (scanSet A B j) : ℤ) + μ₁ (work + j) = (subsetMask (scanSet A B (j + 1)) : ℤ) :=
          by
          rw [hread, hm]
          simp only [Nat.cast_add]
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen ((scanSet A B (j + 1)).card : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc,
                  LightMaskErase.time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hc, LightMaskErase.time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc, LightMaskErase.time] <;> omega)
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
          refine _root_.Light.Ends.setToThen (subsetMask (scanSet A B (j + 1)) : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum,
                  LightMaskErase.time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hsum, LightMaskErase.time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum, LightMaskErase.time] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, erasedB, erasedA, by simp [update_frame_setLocal]⟩
    · have hb : (⟨j, hj⟩ : Fin W) ∉ B := by
        intro hh
        exact hnbitB (by exact_mod_cast (eraseMask_lt_iff B ⟨j, hj⟩).mpr hh)
      have he := scanSet_succ_notMem A B hj hb
      apply Ends.skip
      exact ⟨by simp, erasedB, erasedA, by simp [update_frame_setLocal, he]⟩
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨eB, eA, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨eB, eA, rfl⟩
    have hc := hcard (A ∪ B)
    have hm := hmask (A ∪ B)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen dst ((A ∪ B).card : ℕ) ?_ ?_ ?_
      on_goal -1 =>
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
      refine _root_.Light.Ends.setToThen (subsetMask (A ∪ B) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro i hi
      change Function.update μ₁ dst ((A ∪ B).card : ℤ) (work + i) = _
      rw [Function.update_of_ne (by omega)]
      exact hpowers i hi
    · intro i hi
      change Function.update μ₁ dst ((A ∪ B).card : ℤ) i = _
      rw [Function.update_of_ne (by omega)]
      exact hkept i (Or.inl hi.1)
end ThreeSum.LightMaskUnion
