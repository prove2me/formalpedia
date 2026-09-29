-- Prove2me | solution 1 for WorkbookSource.problem_4319
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:07.955649+00:00
-- url     : https://prove2.me/submissions/7d3f763d-0d57-4e90-8046-8d1051fe3de3

/- InternLM Lean-Workbook, lean_workbook_4319, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d e : ℝ) (h : a * b + b * c + c * a = 12 * d * e) :
    32 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 7 * (a + b + c + d + e) ^ 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := sq_nonneg (a + b + c - 3 * d - 3 * e)
      have := sq_nonneg (a - b)
      have := sq_nonneg (b - c)
      have := sq_nonneg (c - a)
      have := sq_nonneg (d - e)
      have := sq_nonneg (d + e - 2 / 3)
      linarith
  | solve
    | have t := sq_nonneg (a - b)
      have t2 := sq_nonneg (b - c)
      have t3 := sq_nonneg (c - a)
      have t4 := sq_nonneg (d - e)
      have t5 := sq_nonneg (e - d)
      have t6 := sq_nonneg (a + b + c + d + e)
      have t7 := sq_nonneg (a + b + c - 3 * d - 3 * e)
      have t8 := sq_nonneg (a + b + c + 5 * d + 5 * e)
      linarith
  | solve
    | have := sq_nonneg (a + b + c - 3 * d - 3 * e)
      have := sq_nonneg (a - b)
      have := sq_nonneg (b - c)
      have := sq_nonneg (c - a)
      have := sq_nonneg (d - e)
      have := sq_nonneg (d + e - 2 / 3)
      nlinarith
  | solve
    | have t := sq_nonneg (a - b)
      have t2 := sq_nonneg (b - c)
      have t3 := sq_nonneg (c - a)
      have t4 := sq_nonneg (d - e)
      have t5 := sq_nonneg (e - d)
      have t6 := sq_nonneg (a + b + c + d + e)
      have t7 := sq_nonneg (a + b + c - 3 * d - 3 * e)
      have t8 := sq_nonneg (a + b + c + 5 * d + 5 * e)
      nlinarith
example : (∀ (a b c d e : ℝ) (h : a * b + b * c + c * a = 12 * d * e), 32 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 7 * (a + b + c + d + e) ^ 2) := @solution
#print axioms solution
