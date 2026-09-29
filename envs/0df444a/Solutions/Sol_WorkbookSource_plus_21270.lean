-- Prove2me | solution 1 for WorkbookSource.plus_21270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:12.192807+00:00
-- url     : https://prove2.me/submissions/f74e12e0-58b0-4d89-bea9-326eb861d8a6

/- InternLM Lean-Workbook, lean_workbook_plus_21270, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (h₁ : ∀ x, f x = x^2) : ¬ (∀ x y, f x = f y → x = y)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [h₁, sq]
      use 2, -2
      simp
  | solve
    | simp [h₁, pow_two]
      use 1, -1
      norm_num
  | solve
    | simp only [h₁, not_forall]
      use 1, -1
      simp
  | solve
    | simp [h₁, pow_two]
      exact ⟨-1, 1, by norm_num⟩
example : (∀ (f : ℝ → ℝ) (h₁ : ∀ x, f x = x^2), ¬ (∀ x y, f x = f y → x = y)) := @solution
#print axioms solution
