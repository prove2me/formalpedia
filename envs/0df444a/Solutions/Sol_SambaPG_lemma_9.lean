-- Prove2me | solution 1 for SambaPG.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:11:00.579696+00:00
-- url     : https://prove2.me/submissions/89018525-c31f-4f23-8d42-7fe3b25f3bf8

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

private lemma inv_add_one_le_log_sub {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  rw [← Real.log_div (ne_of_gt hx1) (ne_of_gt hx)]
  have h1 : x / (x + 1) ≤ Real.exp (- (1 / (x + 1))) := by
    have := Real.add_one_le_exp (- (1 / (x + 1)))
    have heq : - (1 / (x + 1)) + 1 = x / (x + 1) := by
      field_simp [ne_of_gt hx1]
      ring
    linarith
  have h2 : Real.exp (1 / (x + 1)) ≤ (x + 1) / x := by
    rw [Real.exp_neg] at h1
    have hexp_pos : 0 < Real.exp (1 / (x + 1)) := Real.exp_pos _
    rw [le_inv_comm₀ (div_pos hx hx1) hexp_pos, inv_div] at h1
    exact h1
  have hlog := Real.log_le_log (Real.exp_pos _) h2
  rwa [Real.log_exp] at hlog

theorem solution {A B C : ℝ} (hA : 0 < A) (_hB : 0 < B) (hC : 0 < C) (hBC : 2 * C < B)
    {T : ℕ} (hT : 3 ≤ T) :
    ∑ s ∈ Finset.range T, A / (B + C * s) ≤ A / C * Real.log T := by
  have hterm : ∀ s : ℕ, A / (B + C * s) ≤ A / C * (1 / ((s : ℝ) + 2)) := by
    intro s
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hden1 : 0 < C * ((s : ℝ) + 2) := by positivity
    have hden2 : C * ((s : ℝ) + 2) ≤ B + C * s := by linarith
    have hdiv : A / (B + C * s) ≤ A / (C * ((s : ℝ) + 2)) :=
      div_le_div_of_nonneg_left (le_of_lt hA) hden1 hden2
    have heq : A / (C * ((s : ℝ) + 2)) = A / C * (1 / ((s : ℝ) + 2)) := by
      field_simp [ne_of_gt hC]
    linarith
  have hsum_le : ∑ s ∈ Finset.range T, A / (B + C * s) ≤
      A / C * ∑ s ∈ Finset.range T, (1 / ((s : ℝ) + 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => hterm s)
  suffices hmain : ∑ s ∈ Finset.range T, (1 / ((s : ℝ) + 2)) ≤ Real.log T by
    have hAC : 0 ≤ A / C := div_nonneg (le_of_lt hA) (le_of_lt hC)
    nlinarith
  clear hsum_le hterm hBC _hB hC hA A B C
  induction T, hT using Nat.le_induction with
  | base =>
    have htel : ∑ k ∈ Finset.range 44, (1 / ((22 : ℝ) + k + 1)) ≤
        ∑ k ∈ Finset.range 44, (Real.log ((22 : ℝ) + (k + 1 : ℕ)) - Real.log ((22 : ℝ) + k)) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hk : (0 : ℝ) < 22 + k := by positivity
      have hstep := inv_add_one_le_log_sub hk
      have hcast : (22 : ℝ) + (k + 1 : ℕ) = 22 + (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact hstep
    have htel_eq : ∑ k ∈ Finset.range 44, (Real.log ((22 : ℝ) + (k + 1 : ℕ)) - Real.log ((22 : ℝ) + k)) =
        Real.log 66 - Real.log 22 := by
      have := Finset.sum_range_sub (fun k : ℕ => Real.log ((22 : ℝ) + k)) 44
      norm_num at this ⊢
      exact this
    have hlog66 : Real.log 66 - Real.log 22 = Real.log ((3 : ℕ) : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    have hnum1 : ∑ s ∈ Finset.range 3, (1 / ((s : ℝ) + 2)) = 13 / 12 := by
      repeat' rw [Finset.sum_range_succ]
      rw [Finset.sum_range_zero]
      norm_num
    have hnum2 : (13 / 12 : ℝ) ≤ ∑ k ∈ Finset.range 44, (1 / ((22 : ℝ) + k + 1)) := by
      repeat' rw [Finset.sum_range_succ]
      rw [Finset.sum_range_zero]
      norm_num
    exact (hnum1.le.trans hnum2).trans (htel.trans (htel_eq.trans hlog66).le)
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    have hk_pos : (0 : ℝ) < k := by
      have : 0 < k := by omega
      exact Nat.cast_pos.mpr this
    have hstep1 : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hstep2 : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k :=
      inv_add_one_le_log_sub hk_pos
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
