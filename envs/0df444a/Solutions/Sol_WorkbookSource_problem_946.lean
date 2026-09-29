-- Prove2me | solution 1 for WorkbookSource.problem_946
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:57.03113+00:00
-- url     : https://prove2.me/submissions/49cc41d4-eedb-44d0-87ca-fd456858310b

/- InternLM Lean-Workbook, lean_workbook_946, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | field_simp [pow_succ]
      nlinarith
  | solve
    | simp [h₂, h₁, pow_three]
      nlinarith
  | solve
    | simp [pow_three, h₁, h₂]
      nlinarith
  | solve
    | simp [h₁, h₂, pow_three]
      nlinarith
example : (∀ (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9), c^3 + d^3 = 154) := @solution
#print axioms solution
