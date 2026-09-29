-- Prove2me | solution 1 for WorkbookSource.problem_30377
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:18.118146+00:00
-- url     : https://prove2.me/submissions/6d88f3b2-399d-4d16-99d0-d2c892d72c3d

/- InternLM Lean-Workbook, lean_workbook_30377, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : x^2 - 3*x + 2 = 0 ↔ (x - 1)*(x - 2) = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [sub_mul]
      ring_nf
  | solve
    | field_simp [sub_eq_add_neg]
      ring_nf
  | solve
    | rw [mul_comm]
      rw [← sub_eq_zero]
      ring_nf
  | solve
    | simp [sub_mul, mul_sub, add_comm]
      ring_nf
example : (∀ (x : ℝ), x^2 - 3*x + 2 = 0 ↔ (x - 1)*(x - 2) = 0) := @solution
#print axioms solution
