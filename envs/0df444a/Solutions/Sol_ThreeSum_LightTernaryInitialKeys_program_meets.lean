-- Prove2me | solution 1 for ThreeSum.LightTernaryInitialKeys.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:17.990091+00:00
-- url     : https://prove2.me/submissions/30e0230f-aadb-4c10-beb7-d9b22a21d8be

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryInitialKeys
theorem _root_.solution {lim : Limits} {B nB C nC O nO d : ℕ} (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hBC : B + nB ≤ C) (hCO : C + nC ≤ O) (hO : O + nO ≤ lim.space) (hd : d < lim.depth) :
    Meets lim program 1 d [B, nB, C, nC, O, nO] μ (time nB nC nO)
      (fun r ν =>
        r = 0 ∧ Kept μ ν B ∧ (∀ i < nB, ν (B + i) = 0) ∧ (∀ i < nC, ν (C + i) = 0) ∧ (∀ i < nO, ν (O + i) = 0)) :=
  by
  have hBspace : B + nB ≤ lim.space := by omega
  have hCspace : C + nC ≤ lim.space := by omega
  have h0 := fill_meets (P := program) (μ := μ) (p := 0) (d := d + 1) (dst := B) (n := nB) (x := (0 : ℤ)) rfl hw hBspace
  apply Meets.of_body (by rfl)
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
    first
    | refine _root_.Light.Ends.callToThen (h0 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h0 ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro rb μb ⟨hb, kb⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h1 :=
    fill_meets (P := program) (μ := μb) (p := 0) (d := d + 1) (dst := C) (n := nC) (x := (0 : ℤ)) rfl hw hCspace
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
    | refine _root_.Light.Ends.callToThen (h1 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h1 ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro rc μc ⟨hc, kc⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h2 := fill_meets (P := program) (μ := μc) (p := 0) (d := d + 1) (dst := O) (n := nO) (x := (0 : ℤ)) rfl hw hO
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
    | refine _root_.Light.Ends.callToThen (h2 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h2 ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro ro ν ⟨ho, ko⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change ν x = μ x
    rw [ko x (by omega), kc x (by omega), kb x (by omega)]
  · intro i hi
    change ν (B + i) = 0
    rw [ko _ (by omega), kc _ (by omega)]
    exact (hb i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    change ν (C + i) = 0
    rw [ko _ (by omega)]
    exact (hc i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    exact (ho i (by simpa using hi)).trans (List.getElem_replicate _)
end ThreeSum.LightTernaryInitialKeys
