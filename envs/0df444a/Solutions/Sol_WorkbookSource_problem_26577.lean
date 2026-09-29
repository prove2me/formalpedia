-- Prove2me | solution 1 for WorkbookSource.problem_26577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:40.354034+00:00
-- url     : https://prove2.me/submissions/2aa0e0cd-94ab-4f77-af8f-876c4a223308

/- InternLM Lean-Workbook, lean_workbook_26577, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : x^2 + (x^2 - 1) + (2 - 2*x) + 2*x - 7 = 2*x^2 - 6  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at *
  | solve
    | simp [sq]
      ring
  | solve
    | simp [two_mul]
      ring
  | solve
    | rw [add_comm]
      ring_nf
example : (∀ (x : ℝ), x^2 + (x^2 - 1) + (2 - 2*x) + 2*x - 7 = 2*x^2 - 6) := @solution
#print axioms solution
