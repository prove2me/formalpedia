-- Prove2me | solution 1 for WorkbookSource.problem_2789
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:03.237462+00:00
-- url     : https://prove2.me/submissions/7f7475ed-d40d-416d-abdb-f51b1b126315

/- InternLM Lean-Workbook, lean_workbook_2789, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (h : a + 2 * b + c = a^2 + 2 * b^2 + c^2) : a + 2 * b + c ≤ 4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  | solve
    | simp [h, sq]
      linarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  | solve
    | have h2 := sq_nonneg (a - 1)
      have h3 := sq_nonneg (b - 1)
      have h4 := sq_nonneg (c - 1)
      linarith
  | solve
    | nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  | solve
    | simp [h, sq]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  | solve
    | have h2 := sq_nonneg (a - 1)
      have h3 := sq_nonneg (b - 1)
      have h4 := sq_nonneg (c - 1)
      nlinarith
example : (∀ (a b c : ℝ) (h : a + 2 * b + c = a^2 + 2 * b^2 + c^2), a + 2 * b + c ≤ 4) := @solution
#print axioms solution
