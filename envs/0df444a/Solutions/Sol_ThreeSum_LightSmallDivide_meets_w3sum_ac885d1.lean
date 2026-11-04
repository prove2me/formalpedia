-- Prove2me | solution 1 for ThreeSum.LightSmallDivide.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:31.986036+00:00
-- url     : https://prove2.me/submissions/67b40237-2b6e-4560-bb7a-112a333edc2b

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_whileBlock
import Theorems.Thm_Light_Meets_of_body
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
open ThreeSum ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSmallDivide
theorem _root_.solution {p a b : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ) (hword : ((a + b + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [a, b] μ (time a b) (fun r μ' => r = ((a / b : ℕ) : ℤ) ∧ μ' = μ) :=
  by
  have hdiv : a / b ≤ a := Nat.div_le_self a b
  apply Meets.of_body hp
  unfold body time
  refine Ends.iteLast (fun hbZ => ?_) (fun hzeroZ => ?_)
  · have hbp : (0 : ℤ) < (b : ℤ) := by simpa using hbZ
    have hb : 0 < b := by exact_mod_cast hbp
    have hlast : a < (a / b + 1) * b := by
      have hmod := Nat.mod_lt a hb
      have hsum := Nat.mod_add_div a b
      nlinarith
    have hprod : ∀ i ≤ a / b, (i + 1) * b ≤ a + b := by
      intro i hi
      have hmul := Nat.mul_le_mul_right b hi
      have hh := Nat.div_mul_le_self a b
      nlinarith
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
    refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i], μ⟩) (a / b) (by simp) ?round ?done le_rfl)
    case round =>
      rintro i _ hi rfl
      have hc : (i + 1) * b ≤ a :=
        by
        have hmul := Nat.mul_le_mul_right b (show i + 1 ≤ a / b by omega)
        exact hmul.trans (Nat.div_mul_le_self a b)
      have hcZ : ((i : ℤ) + 1) * (b : ℤ) ≤ (a : ℤ) := by exact_mod_cast hc
      have hnonneg : (0 : ℤ) ≤ ((i : ℤ) + 1) * (b : ℤ) := by positivity
      exact
        ⟨by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
          simp [update_frame_setLocal]⟩
    case done =>
      rintro _ rfl
      have hstop : (a : ℤ) < ((a : ℤ) / (b : ℤ) + 1) * (b : ℤ) := by exact_mod_cast hlast
      have hfit : (((a / b : ℕ) : ℤ) + 1) * (b : ℤ) ≤ (a : ℤ) + (b : ℤ) := by exact_mod_cast hprod (a / b) le_rfl
      have hnonneg : (0 : ℤ) ≤ (((a / b : ℕ) : ℤ) + 1) * (b : ℤ) := by positivity
      have hqnonneg : (0 : ℤ) ≤ (a : ℤ) / (b : ℤ) :=
        by
        rw [← Int.natCast_ediv]
        exact Int.natCast_nonneg _
      have hfitInt : ((a : ℤ) / (b : ℤ) + 1) * (b : ℤ) ≤ (a : ℤ) + (b : ℤ) := by exact_mod_cast hprod (a / b) le_rfl
      refine
        ⟨by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), ?_⟩
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (a / b : ℕ) ?_ ?_ ?_
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
      exact ⟨rfl, rfl⟩
  · have hbp : ¬(0 : ℤ) < (b : ℤ) := by simpa using hzeroZ
    have hb : b = 0 := by omega
    subst b
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
    exact ⟨by simp, rfl⟩
end ThreeSum.LightSmallDivide
