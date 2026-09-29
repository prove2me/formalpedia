-- Prove2me | solution 1 for WorkbookSource.problem_9978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:17.510784+00:00
-- url     : https://prove2.me/submissions/b2bdefb4-e60d-481a-98cf-df8c821d08bf

/- InternLM Lean-Workbook, lean_workbook_9978, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) (h₁ : a^3 - b^3 = 24) (h₂ : a - b = 2) : a^2 + a * b + b^2 = 12  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [h₁, h₂]
  | solve
    | simp [← sub_eq_zero]
      nlinarith
  | solve
    | field_simp [pow_two] at *
      nlinarith
  | solve
    | field_simp [sq, h₂] at h₁ ⊢
      nlinarith
example : (∀ (a b : ℝ) (h₁ : a^3 - b^3 = 24) (h₂ : a - b = 2), a^2 + a * b + b^2 = 12) := @solution
#print axioms solution
