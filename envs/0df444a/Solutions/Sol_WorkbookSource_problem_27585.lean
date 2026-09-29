-- Prove2me | solution 1 for WorkbookSource.problem_27585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:13.277157+00:00
-- url     : https://prove2.me/submissions/9c04481a-4c1c-4b80-8334-2327ea37b0c4

/- InternLM Lean-Workbook, lean_workbook_27585, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf : ∀ x y : ℝ, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) (h₁ : f 1 = 1) : f 0 = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := hf 1 0
      simp [h₁] at this
      linarith
  | solve
    | have h₂ := hf 0 1
      simp [h₁, h₂] at *
      linarith
  | solve
    | specialize hf 0 1
      simp [h₁, hf] at *
      linarith
  | solve
    | have h₂ := hf 0 0
      simp [h₁, h₂] at *
      linarith
  | solve
    | have := hf 1 0
      simp [h₁] at this
      nlinarith
  | solve
    | have h₂ := hf 0 1
      simp [h₁, h₂] at *
      nlinarith
  | solve
    | specialize hf 0 1
      simp [h₁, hf] at *
      nlinarith
  | solve
    | have h₂ := hf 0 0
      simp [h₁, h₂] at *
      nlinarith
example : (∀ (f : ℝ → ℝ) (hf : ∀ x y : ℝ, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) (h₁ : f 1 = 1), f 0 = 0) := @solution
#print axioms solution
