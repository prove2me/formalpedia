-- Prove2me | solution 1 for WorkbookSource.problem_23850
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:31.962715+00:00
-- url     : https://prove2.me/submissions/03e7c793-92f4-46bd-b159-dfa066957bbe

/- InternLM Lean-Workbook, lean_workbook_23850, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z a : ℝ) (h₁ : x = a) (h₂ : 2 * a - 3 * y + z ^ 2 = 1) : y = 1 / 3 * z ^ 2 + (2 * a - 1) / 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | subst h₁
      linarith
  | solve
    | linarith [h₁, h₂]
  | solve
    | nlinarith [h₁, h₂]
  | solve
    | subst x
      linarith [h₂]
  | solve
    | subst h₁
      nlinarith
  | solve
    | nlinarith [h₁, h₂]
  | solve
    | subst x
      nlinarith [h₂]
example : (∀ (x y z a : ℝ) (h₁ : x = a) (h₂ : 2 * a - 3 * y + z ^ 2 = 1), y = 1 / 3 * z ^ 2 + (2 * a - 1) / 3) := @solution
#print axioms solution
