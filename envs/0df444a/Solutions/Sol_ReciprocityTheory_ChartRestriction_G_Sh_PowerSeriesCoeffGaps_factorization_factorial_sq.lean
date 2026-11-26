-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.factorization_factorial_sq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:12:18.840674+00:00
-- url     : https://prove2.me/submissions/230bcb82-19de-4178-bbda-f6d053de7418

import Mathlib

open Nat

private lemma factorization_factorial_self {p : ℕ} (hp : p.Prime) :
    p.factorial.factorization p = 1 := by
  have hp0 : 0 < p := hp.pos
  have hsp : p.pred + 1 = p := succ_pred_eq_of_pos hp0
  rw [← hsp, factorial_succ, hsp]
  rw [Nat.factorization_mul (ne_of_gt hp0) (factorial_ne_zero _)]
  simp [hp.factorization_self]
  exact factorization_factorial_eq_zero_of_lt (sub_one_lt (ne_of_gt hp0))

theorem solution {p : ℕ} (hp : p.Prime) : (p ^ 2).factorial.factorization p = p + 1 := by
  rw [pow_two, factorization_factorial_mul hp, factorization_factorial_self hp, add_comm]
