-- Prove2me | solution 1 for WorkbookSource.problem_6261
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:12.94844+00:00
-- url     : https://prove2.me/submissions/5fe55b95-fc5f-43b5-82ca-8d68984a208e

/- InternLM Lean-Workbook, lean_workbook_6261, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, f (x - 1) = f (-x))
  (h₁ : ∀ x, f x = 3 * f (x - 1)) :
  f = λ _ => 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ext x
      have h₂ := h₁ x
      have h₃ := h₁ (-x)
      simp [h₀] at h₂ h₃
      linarith
  | solve
    | ext x
      have h₂ := h₁ x
      have h₃ := h₁ (-x)
      simp [h₀] at h₂ h₃
      nlinarith
example : (∀ (f : ℝ → ℝ)
  (h₀ : ∀ x, f (x - 1) = f (-x))
  (h₁ : ∀ x, f x = 3 * f (x - 1)), f = λ _ => 0) := @solution
#print axioms solution
