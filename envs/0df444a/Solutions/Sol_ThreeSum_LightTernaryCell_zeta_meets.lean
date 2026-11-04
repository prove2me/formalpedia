-- Prove2me | solution 1 for ThreeSum.LightTernaryCell.zeta_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:09.725927+00:00
-- url     : https://prove2.me/submissions/d632e3e8-49f3-433b-b328-ffe5aeedbca1

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCell
open Light ThreeSum.TernaryQuery
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryCell
theorem _root_.solution {p : ℕ} (hp : P[p]? = some zetaBody) {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ} (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2) (hf : ∀ e, |f e| ≤ U)
    (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim P p d [q.val, a0, a1, a2] μ time (fun r μ' => r = zetaDigit f q ∧ μ' = μ) :=
  by
  have hb0 := abs_le.mp (hf 0)
  have hb1 := abs_le.mp (hf 1)
  have hb2 := abs_le.mp (hf 2)
  apply Meets.of_body hp
  unfold zetaBody time
  fin_cases q
  · refine
      Ends.iteLast (fun hc => ?_) (fun hc => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (f 0) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr0]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hr0] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr0] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [zetaDigit], rfl⟩
    · exfalso
      exact hc (by simp)
  · refine
      Ends.iteLast (fun hc => ?_) (fun hc => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    · exfalso
      norm_num at hc
    · refine
        Ends.iteLast (fun hc => ?_) (fun hc => ?_)
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (f 0 + f 1) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr0, hr1]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hr0, hr1] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr0, hr1] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [zetaDigit], rfl⟩
      · exfalso
        exact hc (by simp)
  · refine
      Ends.iteLast (fun hc => ?_) (fun hc => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    · exfalso
      norm_num at hc
    · refine
        Ends.iteLast (fun hc => ?_) (fun hc => ?_)
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
      · exfalso
        norm_num at hc
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (f 0 + 2 * f 1 + f 2) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr0, hr1, hr2]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hr0, hr1, hr2] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr0, hr1, hr2] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [zetaDigit, Fin.ext_iff], rfl⟩
end ThreeSum.LightTernaryCell
