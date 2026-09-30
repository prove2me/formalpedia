-- Prove2me | solution 1 for SzemerediTrotter.Incidence.inequality_1_no_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:49:17.1654+00:00
-- url     : https://prove2.me/submissions/a0a02691-fd66-4851-98d7-c3edbec977fe

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
    (0.6 : ℝ) * x + (1 - x) ^ (2 / 3 : ℝ) ≤ 1 := by
  intro x hx hhalf
  have h := rpow_one_add_le_one_add_mul_self (s := -x)
    (p := (2 / 3 : ℝ)) (by linarith) (by norm_num) (by norm_num)
  simp only [← sub_eq_add_neg] at h
  linarith

