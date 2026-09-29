-- Prove2me | solution 1 for WorkbookSource.problem_3002
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:04.060726+00:00
-- url     : https://prove2.me/submissions/5a86abe4-03ef-4f02-9d61-6cf50238d853

/- InternLM Lean-Workbook, lean_workbook_3002, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : x + 1.5 > 0 ↔ x > -1.5  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      all_goals intro h; linarith
  | solve
    | constructor
      intro h
      linarith
      intro h
      linarith
  | solve
    | field_simp
      constructor <;> intro h <;> linarith
  | solve
    | constructor
      all_goals intro h
      linarith
      linarith
  | solve
    | constructor
      all_goals intro h; nlinarith
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
  | solve
    | field_simp
      constructor <;> intro h <;> nlinarith
  | solve
    | constructor
      all_goals intro h
      nlinarith
      nlinarith
example : (∀ (x : ℝ), x + 1.5 > 0 ↔ x > -1.5) := @solution
#print axioms solution
