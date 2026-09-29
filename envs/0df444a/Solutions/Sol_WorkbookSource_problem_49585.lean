-- Prove2me | solution 1 for WorkbookSource.problem_49585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:54.293849+00:00
-- url     : https://prove2.me/submissions/470a3d86-8a28-4330-8c68-9921c720ee75

/- InternLM Lean-Workbook, lean_workbook_49585, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (h : 3 * x < π) : x < π / 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [h]
  | solve
    | linarith only [h]
  | solve
    | nlinarith only [h]
  | solve
    | linarith [pi_pos, h]
  | solve
    | nlinarith [h]
  | solve
    | nlinarith only [h]
  | solve
    | nlinarith [pi_pos, h]
example : (∀ (x : ℝ) (h : 3 * x < π), x < π / 3) := @solution
#print axioms solution
