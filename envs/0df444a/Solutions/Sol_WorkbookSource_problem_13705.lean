-- Prove2me | solution 1 for WorkbookSource.problem_13705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:27.564994+00:00
-- url     : https://prove2.me/submissions/71c4125b-642f-4efb-887d-f575e384e468

/- InternLM Lean-Workbook, lean_workbook_13705, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution {a b c x y : ℝ} (h₁ : a ≥ b ∧ b ≥ c) (h₂ : x = a - b) (h₃ : y = b - c) : (x + y + (x + y))^2 ≥ 2 * (x^2 + y^2 + (x + y)^2)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp only [h₂, h₃]
      nlinarith
  | solve
    | simp [h₁, h₂, h₃]
      ring_nf
      nlinarith
  | solve
    | subst h₂ h₃
      simp [add_sq]
      nlinarith
  | solve
    | simp [h₁, h₂, h₃, pow_two]
      nlinarith
example : (∀ {a b c x y : ℝ} (h₁ : a ≥ b ∧ b ≥ c) (h₂ : x = a - b) (h₃ : y = b - c), (x + y + (x + y))^2 ≥ 2 * (x^2 + y^2 + (x + y)^2)) := @solution
#print axioms solution
