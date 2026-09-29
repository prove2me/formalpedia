-- Prove2me | solution 1 for WorkbookSource.problem_31836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:22.119264+00:00
-- url     : https://prove2.me/submissions/17b80d03-fffb-4a29-ab45-4ba1bac369fc

/- InternLM Lean-Workbook, lean_workbook_31836, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c d x : ℝ)
  (h₀ : a * c = 8)
  (h₁ : b * d = -5)
  (h₂ : (a * d + b * c) = -18)
  (h₃ : x = (a + b) * (c + d)) :
  8 * x^2 - 18 * x - 5 = (2 * x - 5) * (4 * x + 1)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [h₃] at *
      ring
  | solve
    | rw [h₃] at *
      ring_nf
  | solve
    | simp [h₀, h₁, h₂, h₃]
      ring
  | solve
    | simp [h₀, h₁, h₂, h₃]; ring
example : (∀ (a b c d x : ℝ)
  (h₀ : a * c = 8)
  (h₁ : b * d = -5)
  (h₂ : (a * d + b * c) = -18)
  (h₃ : x = (a + b) * (c + d)), 8 * x^2 - 18 * x - 5 = (2 * x - 5) * (4 * x + 1)) := @solution
#print axioms solution
