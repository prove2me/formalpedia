-- Prove2me | solution 1 for ThreeSum.LightTernaryCommitKeys.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:19.074606+00:00
-- url     : https://prove2.me/submissions/e089a5bd-7147-4bd6-97da-f036e8142707

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_copy_meets
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
open ThreeSum ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryCommitKeys
theorem _root_.solution {lim : Limits} {Bnew Bold nB Cnew Cold nC Onew Oold nO d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hBC : Bold + nB ≤ Cold) (hCO : Cold + nC ≤ Oold) (hOB : Oold + nO ≤ Bnew)
    (hOC : Oold + nO ≤ Cnew) (hOO : Oold + nO ≤ Onew) (hB : Bnew + nB ≤ lim.space) (hC : Cnew + nC ≤ lim.space)
    (hO : Onew + nO ≤ lim.space) (hd : d < lim.depth) :
    Meets lim program 1 d [Bnew, Bold, nB, Cnew, Cold, nC, Onew, Oold, nO] μ (time nB nC nO)
      (fun r ν =>
        r = 0 ∧
          Kept μ ν Bold ∧
            (∀ i < nB, ν (Bold + i) = μ (Bnew + i)) ∧
              (∀ i < nC, ν (Cold + i) = μ (Cnew + i)) ∧
                (∀ i < nO, ν (Oold + i) = μ (Onew + i)) ∧ (∀ x, Oold + nO ≤ x → ν x = μ x)) :=
  by
  have hBold : Bold + nB ≤ lim.space := by omega
  have hCold : Cold + nC ≤ lim.space := by omega
  have hOold : Oold + nO ≤ lim.space := by omega
  have h0 :=
    copy_meets (P := program) (μ := μ) (p := 0) (d := d + 1) (src := Bnew) (dst := Bold) (n := nB) rfl hw hB hBold
      (Or.inr (by omega))
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
    copy_meets (P := program) (μ := μb) (p := 0) (d := d + 1) (src := Cnew) (dst := Cold) (n := nC) rfl hw hC hCold
      (Or.inr (by omega))
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
  have h2 :=
    copy_meets (P := program) (μ := μc) (p := 0) (d := d + 1) (src := Onew) (dst := Oold) (n := nO) rfl hw hO hOold
      (Or.inr (by omega))
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
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change ν x = μ x
    rw [ko x (by omega), kc x (by omega), kb x (by omega)]
  · intro i hi
    change ν (Bold + i) = μ (Bnew + i)
    rw [ko _ (by omega), kc _ (by omega), hb i hi]
  · intro i hi
    change ν (Cold + i) = μ (Cnew + i)
    rw [ko _ (by omega), hc i hi, kb _ (by omega)]
  · intro i hi
    change ν (Oold + i) = μ (Onew + i)
    rw [ho i hi, kc _ (by omega), kb _ (by omega)]
  · intro x hx
    change ν x = μ x
    rw [ko x (by omega), kc x (by omega), kb x (by omega)]
end ThreeSum.LightTernaryCommitKeys
