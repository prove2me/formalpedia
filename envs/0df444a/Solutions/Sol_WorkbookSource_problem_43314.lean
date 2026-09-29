-- Prove2me | solution 1 for WorkbookSource.problem_43314
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:56.742592+00:00
-- url     : https://prove2.me/submissions/574c92fe-bafc-4199-bb66-0738f9d199d1

/- InternLM Lean-Workbook, lean_workbook_43314, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (h : 1 ≤ x*y - z^2) : (x + 2*y)^2 ≥ (y + 2*z)^2 + 6  := by
  first
  | solve
    | nlinarith [sq_nonneg (x-y),sq_nonneg (y-2*z)]
  | solve
    | field_simp [sq]
      linarith [sq_nonneg (x - y), sq_nonneg (y - z)]
example : (∀ (x y z : ℝ) (h : 1 ≤ x*y - z^2), (x + 2*y)^2 ≥ (y + 2*z)^2 + 6) := @solution
#print axioms solution
