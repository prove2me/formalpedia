-- Prove2me | solution 1 for WorkbookSource.problem_45148
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:10.178852+00:00
-- url     : https://prove2.me/submissions/b75c1fae-aab9-4256-82c1-a3b53c44f822

/- InternLM Lean-Workbook, lean_workbook_45148, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
  4 * (x^3 + 1) ≥ (x + 1)^3 - (x - 1)^3  := by
  first
  | solve
    | nlinarith [mul_nonneg (sq_nonneg (x-1)) (show 0 ≤ 2*x+1 by linarith [hx.1])]
  | solve
    | nlinarith [pow_two_nonneg x, pow_two_nonneg (x - 1), pow_two_nonneg (x + 1)]
  | solve
    | simp [pow_three, mul_add, mul_comm, mul_left_comm]
      nlinarith [hx.1, hx.2]
  | solve
    | nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), hx.1]
example : (∀ (x : ℝ) (hx : 0 ≤ x ∧ x < 1), 4 * (x^3 + 1) ≥ (x + 1)^3 - (x - 1)^3) := @solution
#print axioms solution
