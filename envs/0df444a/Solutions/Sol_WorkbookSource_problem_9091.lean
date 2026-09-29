-- Prove2me | solution 1 for WorkbookSource.problem_9091
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:09.984777+00:00
-- url     : https://prove2.me/submissions/f554bca7-307d-42b3-889a-3bb3741fae27

/- InternLM Lean-Workbook, lean_workbook_9091, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : (1 / 4) * (π ^ 2 / 8 - 2 * (π / 8)) = π ^ 2 / 32 - π / 16  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at x ⊢
  | solve
    | linarith [pi_pos]
  | solve
    | nlinarith [π ^ 2]
  | solve
    | nlinarith [pi_pos]
  | solve
    | nlinarith [pi_pos]
example : (∀ (x : ℝ), (1 / 4) * (π ^ 2 / 8 - 2 * (π / 8)) = π ^ 2 / 32 - π / 16) := @solution
#print axioms solution
