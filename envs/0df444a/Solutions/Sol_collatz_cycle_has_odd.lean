-- Prove2me | solution 1 for collatz_cycle_has_odd
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:30:24.919215+00:00
-- url     : https://prove2.me/submissions/5220adf2-5380-44c8-bd9a-74632f520108

import Mathlib
import Definitions.Def_collatzStepMap
import Theorems.Thm_collatz_iterate_pos

theorem solution (x p : ℕ) (hx : 0 < x) (hp : 0 < p) (hcyc : collatzStep^[p] x = x) :
    ∃ i : ℕ, ¬ Even (collatzStep^[i] x) := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ i, 0 < collatzStep^[i] x := fun i => collatz_iterate_pos i x hx
  -- an all-even orbit halves at every step, so it strictly decreases
  have hdec : ∀ i, collatzStep^[i + 1] x < collatzStep^[i] x := by
    intro i
    have hstep : collatzStep^[i + 1] x = collatzStep^[i] x / 2 := by
      rw [Function.iterate_succ_apply']
      simp [collatzStep, hcon i]
    rw [hstep]
    exact Nat.div_lt_self (hpos i) (by norm_num)
  have hlt : ∀ k, 1 ≤ k → collatzStep^[k] x < x := by
    intro k
    induction k with
    | zero => omega
    | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hdec 0
      · exact lt_trans (hdec n) (ih hn)
  have := hlt p hp
  omega
