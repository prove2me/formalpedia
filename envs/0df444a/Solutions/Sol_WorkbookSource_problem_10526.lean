-- Prove2me | solution 1 for WorkbookSource.problem_10526
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:12.604481+00:00
-- url     : https://prove2.me/submissions/4009501a-4185-4e40-83c0-720ee5035b31

/- InternLM Lean-Workbook, lean_workbook_10526, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0)
  (h₂ : a ≠ b) :
  (a⁻¹ * b⁻¹) / (a⁻¹ ^ 3 - b⁻¹ ^ 3) = 1 / ((1 / a^3) - (1 / b^3)) * (1 / (a * b))  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at h₀ h₁ h₂ ⊢
  | solve
    | field_simp [h₀, h₁, h₂, pow_three]
      ring
  | solve
    | field_simp [h₀, h₁, h₂]
      simp [pow_three]
      ring
  | solve
    | field_simp [h₀, h₁, h₂]
      linear_combination (a - b) * (a^2 + a * b + b^2)
example : (∀ (a b : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0)
  (h₂ : a ≠ b), (a⁻¹ * b⁻¹) / (a⁻¹ ^ 3 - b⁻¹ ^ 3) = 1 / ((1 / a^3) - (1 / b^3)) * (1 / (a * b))) := @solution
#print axioms solution
