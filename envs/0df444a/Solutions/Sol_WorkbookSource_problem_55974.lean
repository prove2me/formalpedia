-- Prove2me | solution 1 for WorkbookSource.problem_55974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:00.71433+00:00
-- url     : https://prove2.me/submissions/239182ac-220a-4d21-b33d-c29eb2f4e66b

/- Source: InternLM Lean-Workbook lean_workbook_55974, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a b c : ℝ) (h1 : a + b + c ≥ 3) (h2 : a > 0 ∧ b > 0 ∧ c > 0): a^2 + b^2 + c^2 ≥ a + b + c := by
  nlinarith [sq_nonneg (a-1), sq_nonneg (b-1), sq_nonneg (c-1)]

example : (∀ (a b c : ℝ) (h1 : a + b + c ≥ 3) (h2 : a > 0 ∧ b > 0 ∧ c > 0), a^2 + b^2 + c^2 ≥ a + b + c) := @solution
#print axioms solution
