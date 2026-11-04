-- Prove2me | solution 1 for ThreeSum.LightCoverGreedy.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:25.475983+00:00
-- url     : https://prove2.me/submissions/86ec37dd-b763-4556-aa20-f8e9c340cb86

import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BooleanGreedy_active_le
import Definitions.Def_WeightedCache3SUM_Alias_531dd71f468e937c
import Theorems.Thm_ThreeSum_BooleanGreedy_active_zero
import Definitions.Def_WeightedCache3SUM_Alias_cd2e9e4e2f0b560e
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_lt
import Theorems.Thm_ThreeSum_BooleanGreedy_choices_length
import Theorems.Thm_ThreeSum_BooleanGreedy_choices_succ
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverGreedy
open Light BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverGreedy
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hrows : 0 < rows)
    (hsrc : src + rows * cols ≤ activePtr) (hspace : activePtr + total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src + i * cols + j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src, activePtr, rows, cols, rounds] μ (time rows cols rounds)
      (fun r μ' =>
        r = (out activePtr rows cols : ℤ) ∧
          Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
            (∀ j < cols, μ' (activePtr + j) = (active matrix rows cols rounds j : ℤ)) ∧
              SameOutside μ μ' activePtr (total rows cols rounds)) :=
  by
  have hspace' : activePtr + cols + rows + rounds ≤ lim.space := by simpa [total, Nat.add_assoc] using hspace
  have hworkSpace : activePtr + cols + rows ≤ lim.space := by omega
  have hactiveSpace : activePtr + cols ≤ lim.space := by omega
  have houtSpace : out activePtr rows cols + rounds ≤ lim.space := by simpa [out] using hspace'
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
    refine _root_.Light.Ends.setToThen (activePtr + cols : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, out, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [out, roundTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, out, roundTime] <;> omega)
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
    refine _root_.Light.Ends.setToThen (out activePtr rows cols : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, out, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [out, roundTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, out, roundTime] <;> omega)
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols) (x := 1) S.fill hw hactiveSpace) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols) (x := 1) S.fill hw hactiveSpace) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, out, roundTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [out, roundTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, out, roundTime] <;> omega)
    on_goal -1 => (rintro vf μ₁ ⟨hfill, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine
    Ends.pieceThen
      (Ends.for (T := rounds * (roundTime rows cols + 8) + 6) (Q := fun σ =>
        Inv μ matrix src activePtr rows cols rounds rounds σ) (Inv μ matrix src activePtr rows cols rounds) rounds
        (roundTime rows cols) ?_ ?_ ?_ ?_ (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?_
  · refine ⟨0, vf, μ₁, ?_, ?_, ?_, ?_⟩
    · simp [Inv, update_frame_setLocal, out]
    · intro j hj
      rw [active_zero hj]
      exact (hfill j (by simpa using hj)).trans (List.getElem_replicate ..)
    · simp [choices, Cover.greedyChoices]
    · exact hkept.mono le_rfl (by unfold total; omega)
  · rintro i _ hi _ ⟨r, v, μ', rfl, hactive, written, kept⟩
    have hmread : ∀ a < rows, ∀ j < cols, μ' (src + a * cols + j) = (matrix a j : ℤ) :=
      by
      intro a ha j hj
      have hm : (a + 1) * cols ≤ rows * cols := Nat.mul_le_mul_right cols (by omega)
      have haddr : src + a * cols + j < activePtr := by nlinarith
      rw [kept _ (Or.inl haddr)]
      exact hread a ha j hj
    have hchoice := choice_lt (matrix := matrix) (cols := cols) hrows i
    have hcWord : (choice matrix rows cols i : ℤ) ≤ lim.word :=
      by
      have hh : choice matrix rows cols i ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    unfold roundBody
    have hs :=
      S.select.meets (d := d + 1) (μ := μ') (src := src) (activePtr := activePtr) (work := activePtr + cols) (rows :=
        rows) (cols := cols) matrix (active matrix rows cols i) hw (by omega) hrows (by omega) le_rfl hworkSpace hmread
        hactive hmatrix (fun j _ => active_le matrix rows cols i j) hword
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
      | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, roundTime,
              LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time,
              LightMinimum.time, out]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [roundTime, LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time,
                LightMinimum.time, out] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, roundTime, LightCoverSelect.time,
              LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time, out] <;>
            omega)
      on_goal -1 => (rintro selected μ₂ ⟨hselected, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hselected' : selected = (choice matrix rows cols i : ℤ) := by rw [hselected, choice_eq_least hrows hmatrix i]
    have hactive₂ : ∀ j < cols, μ₂ (activePtr + j) = (active matrix rows cols i j : ℤ) :=
      by
      intro j hj
      rw [hkeep₂ _ (Or.inl (by omega))]
      exact hactive j hj
    have hwritten₂ : Seg μ₂ (out activePtr rows cols) ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) :=
      written.of_sameOutside hkeep₂ (Or.inr (by unfold out; omega))
    have hkeep₂full : SameOutside μ μ₂ activePtr (total rows cols rounds) :=
      by
      intro a ha
      rw [hkeep₂ _ (by unfold total at ha; omega)]
      exact kept a ha
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (out activePtr rows cols + i) (choice matrix rows cols i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselected',
              roundTime, LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time,
              LightMinimum.time, out]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hselected', roundTime, LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time,
                LightCoverUpdate.time, LightMinimum.time, out] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselected', roundTime, LightCoverSelect.time,
              LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time, out] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    let μ₃ := Function.update μ₂ (out activePtr rows cols + i) (choice matrix rows cols i : ℤ)
    have hchoices₃ : Seg μ₃ (out activePtr rows cols) ((choices matrix rows cols (i + 1)).map (fun x : ℕ => (x : ℤ))) :=
      by
      have hh := hwritten₂.snoc (choice matrix rows cols i : ℤ)
      simpa [choices_succ, List.map_append, List.map_singleton, choices_length, μ₃] using hh
    have hactive₃ : ∀ j < cols, μ₃ (activePtr + j) = (active matrix rows cols i j : ℤ) :=
      by
      intro j hj
      rw [show μ₃ (activePtr + j) = μ₂ (activePtr + j) by unfold μ₃; rw [Function.update_of_ne (by unfold out; omega)]]
      exact hactive₂ j hj
    have hkeep₃ : SameOutside μ μ₃ activePtr (total rows cols rounds) :=
      hkeep₂full.update ⟨by unfold out; omega, by unfold out total; omega⟩ _
    have hmul : (choice matrix rows cols i + 1) * cols ≤ rows * cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src + choice matrix rows cols i * cols + cols ≤ activePtr := by nlinarith
    have hrowSpace : src + choice matrix rows cols i * cols + cols ≤ lim.space := by omega
    have hrowRead :
      ∀ j < cols, μ₃ (src + choice matrix rows cols i * cols + j) = (matrix (choice matrix rows cols i) j : ℤ) :=
      by
      intro j hj
      rw [hkeep₃ _ (Or.inl (by omega))]
      exact hread _ hchoice j hj
    have hmulWord : ((choice matrix rows cols i * cols : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : choice matrix rows cols i * cols ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((src : ℤ) + (choice matrix rows cols i : ℤ) * cols).toNat = src + choice matrix rows cols i * cols :=
      by rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]
    have hu :=
      LightCoverUpdate.meets (d := d + 1) (μ := μ₃) (row := src + choice matrix rows cols i * cols) (activePtr :=
        activePtr) (n := cols) S.update (matrix (choice matrix rows cols i)) (active matrix rows cols i) hw hrowSpace
        hactiveSpace (Or.inl hrow) hrowRead hactive₃ (hmatrix _ hchoice) (fun j _ => active_le matrix rows cols i j)
        hword
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
      | refine _root_.Light.Ends.callToThen (hu _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hu ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselected', haddr,
              μ₃, roundTime, LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time,
              LightMinimum.time, out]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hselected', haddr, μ₃, roundTime, LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time,
                LightCoverUpdate.time, LightMinimum.time, out] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselected', haddr, μ₃, roundTime,
              LightCoverSelect.time, LightCoverScores.time, LightBooleanDot.time, LightCoverUpdate.time,
              LightMinimum.time, out] <;>
            omega)
      on_goal -1 => (rintro vnew μ₄ ⟨hnewActive, hkeep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, selected, vnew, μ₄, by simp [update_frame_setLocal], ?_, ?_, ?_⟩
    · intro j hj
      rw [hnewActive j hj, active_succ hrows hmatrix i j hj]
    · exact hchoices₃.of_sameOutside hkeep₄ (Or.inr (by unfold out; omega))
    · intro a ha
      rw [hkeep₄ _ (by unfold total at ha; omega)]
      exact hkeep₃ a ha
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ _ _ ⟨r, v, μ', rfl, _, _, _⟩
    simp
  · rintro σ ⟨r, v, μ', rfl, hactive, written, kept⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (out activePtr rows cols : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, out, roundTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [out, roundTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, out, roundTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, written, hactive, kept⟩
end Procs
end ThreeSum.LightCoverGreedy
