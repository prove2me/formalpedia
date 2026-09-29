-- Prove2me | solution 1 for WorkbookSource.problem_56440
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:01.572072+00:00
-- url     : https://prove2.me/submissions/b5c6368f-1752-43d0-83f0-c70efba150f4

/- Source: InternLM Lean-Workbook lean_workbook_56440, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (α : ℝ) (h₁ : cos α = 4/5) (h₂ : sin α = 3/5) : cos (2*α) = 7/25 ∧ sin (2*α) = 24/25 := by
  constructor
  · rw [Real.cos_two_mul]
    norm_num [h₁]
  · rw [Real.sin_two_mul]
    norm_num [h₁,h₂]

example : (∀ (α : ℝ) (h₁ : cos α = 4/5) (h₂ : sin α = 3/5), cos (2*α) = 7/25 ∧ sin (2*α) = 24/25) := @solution
#print axioms solution
