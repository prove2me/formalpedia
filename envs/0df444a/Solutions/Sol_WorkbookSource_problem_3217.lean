-- Prove2me | solution 1 for WorkbookSource.problem_3217
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:14:56.584837+00:00
-- url     : https://prove2.me/submissions/c3668675-7261-488a-b39a-ec434579d00e

/- Source: InternLM Lean-Workbook lean_workbook_3217, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (f : ℤ → ℤ) (f_def : ∀ x, f x = x^5 + 5 * x^4 + 10 * x^3 + 10 * x^2 - 2 * x + 1) : f (-2021) + f (2019) = 14 := by
  simp only [f_def]
  norm_num

example : (∀ (f : ℤ → ℤ) (f_def : ∀ x, f x = x^5 + 5 * x^4 + 10 * x^3 + 10 * x^2 - 2 * x + 1), f (-2021) + f (2019) = 14) := @solution
#print axioms solution
