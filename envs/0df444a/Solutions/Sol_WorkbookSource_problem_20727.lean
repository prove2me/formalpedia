-- Prove2me | solution 1 for WorkbookSource.problem_20727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:00.175635+00:00
-- url     : https://prove2.me/submissions/4faa3bfc-3ae2-4379-bd65-1be711bc5044

/- InternLM Lean-Workbook, lean_workbook_20727, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = 2 * a)
  (h₁ : y = 2 * b)
  (h₂ : z = 2 * c)
  (h₃ : x^2 + y^2 + z^2 = 2 * x * y * z) :
  4 * (a^2 + b^2 + c^2) = 16 * a * b * c  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [h₂, h₁, h₀] at h₃
      linarith
  | solve
    | simp [h₀, h₁, h₂] at *
      linarith
  | solve
    | simp [h₀, h₁, h₂] at h₃ ⊢
      linarith
  | solve
    | simp [h₀, h₁, h₂] at *
      linarith [h₃]
  | solve
    | rw [h₂, h₁, h₀] at h₃
      nlinarith
  | solve
    | simp [h₀, h₁, h₂] at *
      nlinarith
  | solve
    | simp [h₀, h₁, h₂] at h₃ ⊢
      nlinarith
  | solve
    | simp [h₀, h₁, h₂] at *
      nlinarith [h₃]
example : (∀ (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = 2 * a)
  (h₁ : y = 2 * b)
  (h₂ : z = 2 * c)
  (h₃ : x^2 + y^2 + z^2 = 2 * x * y * z), 4 * (a^2 + b^2 + c^2) = 16 * a * b * c) := @solution
#print axioms solution
