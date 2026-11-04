-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentBatch.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:03:25.465708+00:00
-- url     : https://prove2.me/submissions/d5b61ed6-6bf1-4adc-8b59-98168c941e33

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_flag_zero
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_flag_succ
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentRow_Procs_meets
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
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.LightTernaryMomentBatch.flag_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryMomentBatch
open Light FiniteMomentZeroDetector
attribute [local instance] Classical.propDecidable
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentBatch
namespace Procs
theorem _root_.solution {H pMain : ℕ} (S : Procs H P pMain) {μ : ℕ → ℤ}
    {records count originalA originalCount matrix scratch U : ℕ} (position t : ℕ → ℕ) (A : ℕ → ℤ)
    (v w : ∀ i, Fin (t i) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hrecords : records + 3 * count ≤ scratch) (hAarray : originalA + originalCount ≤ scratch)
    (hmatrix : matrix + (2 * H + 1) * count ≤ scratch) (hspace : scratch + (2 * H + 1) ≤ lim.space)
    (hpositions : ∀ i < count, position i < originalCount)
    (hpositionRead : ∀ i < count, μ (records + 3 * i) = (position i : ℤ))
    (hAread : ∀ j < originalCount, μ (originalA + j) = A j) (hA : ∀ j < originalCount, |A j| ≤ (U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H) ≤ lim.word) (hv : ∀ i < count, Function.Injective (v i))
    (hweights : ∀ i < count, ∀ s, w i s ≠ 0) (ht : ∀ i < count, t i ≤ H)
    (hmabs : ∀ i < count, ∀ k ≤ 2 * H, |moment (v i) (w i) k| ≤ (U : ℤ))
    (hm : ∀ i < count, ∀ k ≤ 2 * H, μ (matrix + k * count + i) = moment (v i) (w i) k) :
    Meets lim P pMain d [records, count, originalA, originalCount, matrix, scratch] μ (time H count)
      (fun r ν => r = (if ∃ i < count, ∃ s, v i s = A (position i) then 1 else 0 : ℤ) ∧ Kept μ ν scratch) :=
  by
  classical
  let hit : ℕ → Prop := fun i => ∃ s, v i s = A (position i)
  have hflag (i : ℕ) : 0 ≤ flag hit i ∧ flag hit i ≤ 1 :=
    by
    unfold flag
    split_ifs <;> omega
  have h1 : (1 : ℤ) ≤ lim.word := by
    have hlim : (1 : ℕ) ≤ lim.space := by omega
    exact (Int.ofNat_le.mpr hlim).trans hw
  have hcount : (count : ℤ) ≤ lim.word :=
    by
    have hh : count ≤ lim.space := by omega
    exact (Int.ofNat_le.mpr hh).trans hw
  apply Meets.of_body S.main
  unfold body time
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentRow.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentRow.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := count * (LightTernaryMomentRow.time H + 200) + 10) (Q := fun σ =>
        ∃ r ν,
          σ = ⟨frame [records, count, originalA, originalCount, matrix, scratch, flag hit count, count, r], ν⟩ ∧
            Kept μ ν scratch)
        (Inv μ hit records count originalA originalCount matrix scratch) count (LightTernaryMomentRow.time H + 170)
        ?start ?round ?done ?bound (hT := by
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
      ?finish
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl⟩
    simp [Inv, flag_zero, update_frame_setLocal]
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, hkeep⟩
    change i < count at hi
    have him := Nat.mul_le_mul_left 3 (show i + 1 ≤ count by omega)
    simp only [Nat.mul_add, Nat.mul_one] at him
    have hrecord : records + 3 * i + 3 ≤ scratch := by omega
    have hrpos : ν (records + 3 * i) = (position i : ℤ) :=
      by
      rw [hkeep _ (by omega)]
      exact hpositionRead i hi
    have htarget : ν (originalA + position i) = A (position i) :=
      by
      rw [hkeep _ (by have := hpositions i hi; omega)]
      exact hAread _ (hpositions i hi)
    have hmrow : ∀ k ≤ 2 * H, ν (matrix + k * count + i) = moment (v i) (w i) k :=
      by
      intro k hk
      have hmul := Nat.mul_le_mul_right count (show k + 1 ≤ 2 * H + 1 by omega)
      simp only [Nat.add_mul, one_mul] at hmul
      have hmatrix' := hmatrix
      rw [Nat.add_mul, one_mul] at hmatrix'
      rw [hkeep _ (by omega)]
      exact hm i hi k hk
    have hrecordCast : ((records : ℤ) + 3 * (i : ℤ)).toNat = records + 3 * i := by norm_cast
    have hmulWord : (3 : ℤ) * i ≤ lim.word :=
      by
      have hh : 3 * i ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((S.row.meets (d := d + 1) (μ := ν) (record := records + 3 * i) (originalA := originalA) (originalCount :=
                originalCount) (matrix := matrix) (count := count) (row := i) (scratch := scratch) (position :=
                position i) (U := U) (t := t i) (A (position i)) (v i) (w i) hw (by omega) hi (hpositions i hi) hrecord
                hAarray hmatrix hspace hrpos htarget (hA _ (hpositions i hi)) hword (hv i hi) (hweights i hi) (ht i hi)
                (hmabs i hi) hmrow)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (S.row.meets (d := d + 1) (μ := ν) (record := records + 3 * i) (originalA := originalA) (originalCount :=
              originalCount) (matrix := matrix) (count := count) (row := i) (scratch := scratch) (position :=
              position i) (U := U) (t := t i) (A (position i)) (v i) (w i) hw (by omega) hi (hpositions i hi) hrecord
              hAarray hmatrix hspace hrpos htarget (hA _ (hpositions i hi)) hword (hv i hi) (hweights i hi) (ht i hi)
              (hmabs i hi) hmrow)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrecordCast,
              LightTernaryMomentRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrecordCast, LightTernaryMomentRow.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrecordCast, LightTernaryMomentRow.time] <;>
            omega)
      on_goal -1 => (rintro r' ξ ⟨hanswer, hkeepRow⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkept : Kept μ ξ scratch := by
      intro a ha
      exact (hkeepRow a ha).trans (hkeep a ha)
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
        _root_.Light.Ends.iteIffThen ((0 : ℤ) < (if hit i then 1 else 0 : ℤ)) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hanswer, hit,
              LightTernaryMomentRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hanswer, hit, LightTernaryMomentRow.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hanswer, hit, LightTernaryMomentRow.time] <;>
            omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hhit : hit i := by by_contra hn; simp [hn] at hyes
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (1 : ℤ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightTernaryMomentRow.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightTernaryMomentRow.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentRow.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, r', ξ, ?_, hkept⟩
      simp [update_frame_setLocal, flag_succ, hhit]
    · have hmiss : ¬hit i := by intro hh; simp [hh] at hno
      refine Ends.skip ?_
      refine ⟨by simp, r', ξ, ?_, hkept⟩
      simp [update_frame_setLocal, flag_succ, hmiss]
  case done =>
    rintro _ _ ⟨r, ν, rfl, hkeep⟩
    exact ⟨r, ν, rfl, hkeep⟩
  case bound =>
    rintro i _ hi _ ⟨r, ν, rfl, hkeep⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨r, ν, rfl, hkeep⟩
    have hf := hflag count
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag hit count) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightTernaryMomentRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightTernaryMomentRow.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentRow.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [flag, hit], hkeep⟩
end Procs
end ThreeSum.LightTernaryMomentBatch
