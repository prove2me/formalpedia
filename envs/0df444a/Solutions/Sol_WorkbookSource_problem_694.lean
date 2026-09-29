-- Prove2me | solution 1 for WorkbookSource.problem_694
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:55.417195+00:00
-- url     : https://prove2.me/submissions/c3c2bd15-37c7-477a-bfbb-773cf7dfe82d

/- InternLM Lean-Workbook, lean_workbook_694, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (h : x + 600 = 1700) : x = 1100  := by
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
    | exact by linarith [h]
  | solve
    | exact by linarith only [h]
  | solve
    | nlinarith [h]
  | solve
    | nlinarith only [h]
  | solve
    | exact by nlinarith [h]
  | solve
    | exact by nlinarith only [h]
example : (∀ (x : ℝ) (h : x + 600 = 1700), x = 1100) := @solution
#print axioms solution
