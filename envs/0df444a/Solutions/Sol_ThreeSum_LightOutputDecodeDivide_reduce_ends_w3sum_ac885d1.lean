-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDivide.reduce_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:41.652942+00:00
-- url     : https://prove2.me/submissions/51c9165e-9dcb-45ea-a469-b642a9389cfc

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_whileConst
import Theorems.Thm_Light_emodRounds_le
import Theorems.Thm_Light_mul_two_pow_le_iff
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
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}
namespace ThreeSum.LightOutputDecodeDivide
theorem _root_.solution (F : Pre lim Mo V fr) (haV : a ≤ V) {t : ℤ} (tab : Table μ ν Mo fr (emodRounds a Mo)) :
    Ends lim P d reduce ⟨frame [a, Mo, fr, a, emodRounds a Mo, t, 0], ν⟩ (60 * emodRounds a Mo + 4)
      (fun σ => σ = ⟨frame [a, Mo, fr, (a % Mo : ℕ), 0, t, (a / Mo : ℕ)], ν⟩) :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hK := emodRounds_le haV (M := Mo)
  have hgt : a < Mo * 2 ^ (emodRounds a Mo) :=
    not_le.mp fun h => absurd ((mul_two_pow_le_iff F.mod_pos).mp h) (lt_irrefl _)
  refine
    Ends.whileConst
      (fun i σ =>
        ∃ r q : ℕ,
          σ = ⟨frame [a, Mo, fr, r, (emodRounds a Mo - i : ℕ), t, q], ν⟩ ∧
            r < Mo * 2 ^ (emodRounds a Mo - i) ∧ a = q * (Mo * 2 ^ (emodRounds a Mo - i)) + r)
      (emodRounds a Mo) reduceRound.blockCost ?start ?round ?done (by simp [reduceRound]; omega)
  case start => exact ⟨a, 0, by simp, by simpa using hgt, by simp⟩
  case done =>
    rintro _ ⟨r, q, rfl, hr, haq⟩
    rw [Nat.sub_self] at hr haq ⊢
    simp only [pow_zero, Nat.mul_one] at hr haq
    have hq : a / Mo = q := by
      rw [haq, Nat.add_comm, Nat.add_mul_div_right _ _ F.mod_pos, Nat.div_eq_of_lt hr, Nat.zero_add]
    have hr' : a % Mo = r := by
      have hh := Nat.div_add_mod a Mo
      rw [hq] at hh
      nlinarith
    exact ⟨by simp; omega, by simp, by rw [hq, hr']; rfl⟩
  case round =>
    rintro i _ hi ⟨r, q, rfl, hr, haq⟩
    obtain ⟨c, hc⟩ : ∃ c, emodRounds a Mo - i = c + 1 := ⟨emodRounds a Mo - i - 1, by omega⟩
    rw [show emodRounds a Mo - (i + 1) = c by omega]
    rw [hc] at hr haq ⊢
    have hcell : ν (fr + c) = ((Mo * 2 ^ c : ℕ) : ℤ) := tab.1 c (by omega)
    have hmle : Mo * 2 ^ c ≤ a := (mul_two_pow_le_iff F.mod_pos).mpr (by omega)
    have hqle : q ≤ a :=
      by
      have hp : 0 < Mo * 2 ^ (c + 1) := Nat.mul_pos F.mod_pos (Nat.two_pow_pos _)
      have hm := Nat.le_mul_of_pos_right q hp
      omega
    have hrle : r ≤ a := by omega
    have hdouble : Mo * 2 ^ (c + 1) = Mo * 2 ^ c + Mo * 2 ^ c := by ring
    rw [hdouble] at hr haq
    generalize Mo * 2 ^ c = m at hr haq hcell hmle ⊢
    refine
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), ?_⟩
    unfold reduceRound
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (c : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.setToThen (2 * q : ℕ) ?_ ?_ ?_
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
    refine Ends.iteLast (fun h => ?_) (fun h => ?_)
    · have hmr : m ≤ r := by simp [hcell] at h; omega
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (r - m : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcell]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hcell] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcell] <;> omega)
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
        refine _root_.Light.Ends.setToThen (2 * q + 1 : ℕ) ?_ ?_ ?_
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
      refine ⟨r - m, 2 * q + 1, rfl, by omega, ?_⟩
      have hs := Nat.sub_add_cancel hmr
      nlinarith
    · have hrm : r < m := by simp [hcell] at h; omega
      exact Ends.skip ⟨r, 2 * q, rfl, hrm, by nlinarith⟩
end ThreeSum.LightOutputDecodeDivide
