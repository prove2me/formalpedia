-- Prove2me | solution 1 for WorkbookTyped.plus_43951
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:32.866384+00:00
-- url     : https://prove2.me/submissions/230d4587-f3f3-47b9-9408-be73622ab000

/- Source: InternLM Lean-Workbook, lean_workbook_plus_43951. Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
This is an explicit-binder repair, not an unchanged formal declaration.
Added the explicit real binder (x : ℝ). The original formula already uses Real.sqrt, which fixes the intended real equation once its variable is declared. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem solution (x : ℝ) : x^2 - 2*x - 1 = 0 ↔ x = 1 + Real.sqrt 2 ∨ x = 1 - Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hp : (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> rw [h] <;> nlinarith

example : (∀ (x : ℝ), x^2 - 2*x - 1 = 0 ↔ x = 1 + Real.sqrt 2 ∨ x = 1 - Real.sqrt 2) := @solution
#print axioms solution
