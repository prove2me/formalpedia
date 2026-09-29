-- Prove2me | solution 1 for WorkbookSource.problem_21933
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:03.956305+00:00
-- url     : https://prove2.me/submissions/2edb8386-cb83-436b-89de-13bc9fd72d5b

/- InternLM Lean-Workbook, lean_workbook_21933, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x y a : ℝ)
  (h₀ : x = a * y)
  (h₁ : 4 = a * 8)
  (h₂ : y = 10) :
  x = 5  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | subst h₂
      nlinarith
  | solve
    | rw [h₀, h₂]
      linarith
  | solve
    | rw [h₀, h₂] at *
      linarith
  | solve
    | rw [h₀, h₂] at *
      nlinarith
  | solve
    | rw [h₀, h₂]
      nlinarith
  | solve
    | rw [h₀, h₂] at *
      nlinarith
example : (∀ (x y a : ℝ)
  (h₀ : x = a * y)
  (h₁ : 4 = a * 8)
  (h₂ : y = 10), x = 5) := @solution
#print axioms solution
