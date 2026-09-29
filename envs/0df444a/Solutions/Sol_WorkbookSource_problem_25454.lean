-- Prove2me | solution 1 for WorkbookSource.problem_25454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:37.925071+00:00
-- url     : https://prove2.me/submissions/6f19c8a9-b239-4540-93ef-044c5efd1bd2

/- InternLM Lean-Workbook, lean_workbook_25454, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (h₁ : ∀ x, f (x - 2) = x^3) : f 3 = 125  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have h := h₁ 5
      norm_num at h
      exact h
  | solve
    | have h₂ := h₁ 5
      norm_num at *
      exact h₂
  | solve
    | have := h₁ 5
      norm_num at this
      exact this
  | solve
    | have h₂ := h₁ 5
      norm_num at h₁ h₂
      linarith
  | solve
    | have h₂ := h₁ 5
      norm_num at h₁ h₂
      nlinarith
example : (∀ (f : ℝ → ℝ) (h₁ : ∀ x, f (x - 2) = x^3), f 3 = 125) := @solution
#print axioms solution
