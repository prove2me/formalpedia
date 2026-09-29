-- Prove2me | solution 1 for WorkbookSource.problem_31073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:19.567266+00:00
-- url     : https://prove2.me/submissions/527025b9-95d9-4a4b-bd2a-8c4c965bb140

/- InternLM Lean-Workbook, lean_workbook_31073, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (n : ℝ) : n + 2 = n / 2 ↔ n = -4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro h
      linarith
      linarith [h]
  | solve
    | constructor
      intro h
      nlinarith
      rintro rfl
      ring
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      linarith
  | solve
    | constructor <;> intro h
      nlinarith
      linarith [h]
  | solve
    | constructor <;> intro h
      nlinarith
      nlinarith [h]
example : (∀ (n : ℝ), n + 2 = n / 2 ↔ n = -4) := @solution
#print axioms solution
