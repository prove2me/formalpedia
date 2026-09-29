-- Prove2me | solution 1 for WorkbookSource.problem_49999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:37.360754+00:00
-- url     : https://prove2.me/submissions/08e56786-3455-4b4e-8c3d-da6f43f07c92

/- Source: InternLM Lean-Workbook, record lean_workbook_49999.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c d : ℝ) (h₁ : b ≠ 0) (h₂ : d ≠ 0) (h₃ : b + d ≠ 0) : a / b = c / d → (a + c) / (b + d) = a / b := by
  first
  | solve
    | field_simp [h₁, h₂, h₃]
      intro h
      linarith
  | solve
    | rintro h₄
      field_simp [h₁, h₂, h₃] at h₄ ⊢
      linarith
  | solve
    | intro h
      field_simp [h₁, h₂, h₃] at h ⊢
      linarith [h]
  | solve
    | rw [div_eq_div_iff h₁ h₂]
      intro h
      field_simp [h₃]
      linarith
  | solve
    | rintro h
      rw [div_eq_mul_inv] at h
      field_simp [h₁, h₂, h₃] at h ⊢
      linarith
  | solve
    | intro h
      rw [div_eq_mul_inv] at h ⊢
      field_simp [h₁, h₂, h₃] at h ⊢
      linarith

example : (∀ (a b c d : ℝ) (h₁ : b ≠ 0) (h₂ : d ≠ 0) (h₃ : b + d ≠ 0), a / b = c / d → (a + c) / (b + d) = a / b) := @solution
#print axioms solution
