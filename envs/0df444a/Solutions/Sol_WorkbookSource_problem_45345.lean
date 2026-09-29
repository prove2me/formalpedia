-- Prove2me | solution 1 for WorkbookSource.problem_45345
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:12.246111+00:00
-- url     : https://prove2.me/submissions/1720dbb0-60bf-4b5e-b853-c0df93e707d1

/- InternLM Lean-Workbook, lean_workbook_45345, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2) : 3 - 2 * x ^ 2 ≥ x / 2 * (3 * x ^ 2 - 16 * x + 15)  := by
  first
  | solve
    | nlinarith [mul_nonneg (show 0 ≤ 2-x by linarith [hx.2]) (sq_nonneg (x-1))]
  | solve
    | have := sq_nonneg (x - 1)
      have := sq_nonneg (x - 2)
      nlinarith
  | solve
    | nlinarith [sq_nonneg (x - 1), hx]
example : (∀ {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2), 3 - 2 * x ^ 2 ≥ x / 2 * (3 * x ^ 2 - 16 * x + 15)) := @solution
#print axioms solution
