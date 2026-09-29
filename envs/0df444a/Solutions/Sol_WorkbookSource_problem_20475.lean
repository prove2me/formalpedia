-- Prove2me | solution 1 for WorkbookSource.problem_20475
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:15.625776+00:00
-- url     : https://prove2.me/submissions/bb9de7d6-38ca-416a-8a1a-c2b07deb05f7

/- InternLM Lean-Workbook, lean_workbook_20475, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) (n : ℕ) (hn : Odd n) (hab : a + b = 0) : a^n + b^n = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [eq_neg_of_add_eq_zero_right hab]
      simp [add_comm, hn.neg_pow]
  | solve
    | simp only [add_eq_zero_iff_eq_neg] at hab
      simp [hab, hn.neg_pow]
  | solve
    | rw [eq_neg_of_add_eq_zero_right hab]
      rw [add_comm]
      simp [hn.neg_pow, add_comm]
  | solve
    | simp [eq_neg_of_add_eq_zero_right hab, add_comm]
      simp [add_comm a, hab, hn.neg_pow]
example : (∀ (a b : ℝ) (n : ℕ) (hn : Odd n) (hab : a + b = 0), a^n + b^n = 0) := @solution
#print axioms solution
