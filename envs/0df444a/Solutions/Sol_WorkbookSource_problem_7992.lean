-- Prove2me | solution 1 for WorkbookSource.problem_7992
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:35.820679+00:00
-- url     : https://prove2.me/submissions/d4636080-6f39-4386-be32-72dd8392811f

/- InternLM Lean-Workbook, lean_workbook_7992, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x:ℝ) : 2*x+1 >= 0 ↔ x >= -1/2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro hx
      linarith
      linarith
  | solve
    | constructor
      intro h
      linarith
      intro h
      linarith
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
  | solve
    | constructor <;> intro h
      linarith [h]
      linarith [h]
  | solve
    | constructor <;> intro hx
      nlinarith
      nlinarith
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
  | solve
    | constructor <;> intro h
      nlinarith [h]
      nlinarith [h]
example : (∀ (x:ℝ), 2*x+1 >= 0 ↔ x >= -1/2) := @solution
#print axioms solution
