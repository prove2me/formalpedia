-- Prove2me | solution 1 for WorkbookSource.problem_9771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:14.709432+00:00
-- url     : https://prove2.me/submissions/b8d56850-2934-4880-ad1c-9145e93653c6

/- InternLM Lean-Workbook, lean_workbook_9771, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : 4 * (-(Real.cos x) ^ 2 + Real.cos x + 1 / 2) = 4 * (-((Real.cos x) - 1 / 2) ^ 2 + 3 / 4)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sub_sq]
      ring
  | solve
    | simp [add_comm]
      ring
  | solve
    | simp [sub_sq]
      ring_nf
  | solve
    | simp only [sub_sq]
      ring_nf
example : (∀ (x : ℝ), 4 * (-(Real.cos x) ^ 2 + Real.cos x + 1 / 2) = 4 * (-((Real.cos x) - 1 / 2) ^ 2 + 3 / 4)) := @solution
#print axioms solution
