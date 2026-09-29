-- Prove2me | solution 1 for WorkbookSource.problem_12448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:47.781002+00:00
-- url     : https://prove2.me/submissions/59fac649-6885-482f-8c82-c5302daad10e

/- InternLM Lean-Workbook, lean_workbook_12448, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (h : 19 + x = 19) : x = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [h]
  | solve
    | simpa using h
  | solve
    | linarith [h, h]
  | solve
    | nlinarith [h, h]
  | solve
    | nlinarith [h]
  | solve
    | nlinarith [h, h]
example : (∀ (x : ℝ) (h : 19 + x = 19), x = 0) := @solution
#print axioms solution
