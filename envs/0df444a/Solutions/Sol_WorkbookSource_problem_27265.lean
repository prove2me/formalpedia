-- Prove2me | solution 1 for WorkbookSource.problem_27265
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:41.706248+00:00
-- url     : https://prove2.me/submissions/b29f6db4-a25f-4f78-816f-a39e786ce8ab

/- InternLM Lean-Workbook, lean_workbook_27265, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (x + 30) / (x / 55 + 1 / 2) = 50) :
  x = 110  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | field_simp at h₁
      nlinarith
  | solve
    | field_simp at h₁ ⊢
      linarith [h₀]
  | solve
    | field_simp at h₁ ⊢
      linarith [h₁]
  | solve
    | field_simp at h₁
      linarith [h₀, h₁]
  | solve
    | field_simp at h₁ ⊢
      nlinarith [h₀]
  | solve
    | field_simp at h₁ ⊢
      nlinarith [h₁]
  | solve
    | field_simp at h₁
      nlinarith [h₀, h₁]
example : (∀ (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (x + 30) / (x / 55 + 1 / 2) = 50), x = 110) := @solution
#print axioms solution
