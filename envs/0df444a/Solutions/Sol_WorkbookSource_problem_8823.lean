-- Prove2me | solution 1 for WorkbookSource.problem_8823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:08.251662+00:00
-- url     : https://prove2.me/submissions/2954656e-5067-4783-86b1-566f12f776ea

/- InternLM Lean-Workbook, lean_workbook_8823, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) : 4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ↔ (a ^ 3 + b ^ 3) / 2 ≥ ((a + b) / 2) ^ 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro h
      linarith
      linarith
  | solve
    | constructor <;> intro h
      nlinarith
      nlinarith
  | solve
    | constructor <;> intro h
      repeat' nlinarith [h]
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
  | solve
    | constructor <;> intro h
      nlinarith
      nlinarith
example : (∀ (a b : ℝ), 4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ↔ (a ^ 3 + b ^ 3) / 2 ≥ ((a + b) / 2) ^ 3) := @solution
#print axioms solution
