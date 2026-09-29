-- Prove2me | solution 1 for WorkbookSource.problem_8268
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:05.005695+00:00
-- url     : https://prove2.me/submissions/96a2fea5-e437-4f21-89b9-e4b46a07e34e

/- InternLM Lean-Workbook, lean_workbook_8268, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (h : 2 * x + 3 = 7) : x = 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [h]
  | solve
    | nlinarith [h]
  | solve
    | linarith only [h]
  | solve
    | exact by linarith
  | solve
    | nlinarith [h]
  | solve
    | nlinarith only [h]
  | solve
    | exact by nlinarith
example : (∀ (x : ℝ) (h : 2 * x + 3 = 7), x = 2) := @solution
#print axioms solution
