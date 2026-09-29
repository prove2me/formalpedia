-- Prove2me | solution 1 for WorkbookSource.problem_21991
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:04.73391+00:00
-- url     : https://prove2.me/submissions/4cdd85e1-38eb-46cf-84da-ca33e32b4a06

/- InternLM Lean-Workbook, lean_workbook_21991, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c : ℝ) (h₀ : a + b + c ≥ 6) (h₁ : a * b + b * c + c * a ≥ 12) (h₂ : a * b * c ≥ 8) :
  (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 125  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have h₃ : (a - b)^2 + (b - c)^2 + (c - a)^2 ≥ 0 := by nlinarith
      nlinarith
example : (∀ (a b c : ℝ) (h₀ : a + b + c ≥ 6) (h₁ : a * b + b * c + c * a ≥ 12) (h₂ : a * b * c ≥ 8), (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 125) := @solution
#print axioms solution
