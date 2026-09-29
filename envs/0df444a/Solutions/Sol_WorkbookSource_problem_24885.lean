-- Prove2me | solution 1 for WorkbookSource.problem_24885
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:34.645819+00:00
-- url     : https://prove2.me/submissions/fb159fd2-9899-4299-9575-14a29c6427e9

/- InternLM Lean-Workbook, lean_workbook_24885, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) : x^2 - 3*x*y - y^2 + (2*x^2 + 5*x*y - 4*y^2) = 3*x^2 + 2*x*y - 5*y^2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [sq]
      ring
  | solve
    | simp [sq]
      linarith
  | solve
    | rw [add_comm]
      ring
  | solve
    | rw [← eq_comm]
      ring
  | solve
    | simp [sq]
      nlinarith
example : (∀ (x y : ℝ), x^2 - 3*x*y - y^2 + (2*x^2 + 5*x*y - 4*y^2) = 3*x^2 + 2*x*y - 5*y^2) := @solution
#print axioms solution
