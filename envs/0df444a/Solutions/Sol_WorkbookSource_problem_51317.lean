-- Prove2me | solution 1 for WorkbookSource.problem_51317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:59.934139+00:00
-- url     : https://prove2.me/submissions/0e6346fc-98ed-46a9-9004-d01db3830f81

/- InternLM Lean-Workbook, lean_workbook_51317, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a : ℝ) :
  4 * a^2 + 8 * a + 1 = 4 * (a + 1)^2 - 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sq]
      ring
  | solve
    | rw [mul_comm]
      ring
  | solve
    | rw [add_comm]
      ring
  | solve
    | simp [pow_two]
      ring
example : (∀ (a : ℝ), 4 * a^2 + 8 * a + 1 = 4 * (a + 1)^2 - 3) := @solution
#print axioms solution
