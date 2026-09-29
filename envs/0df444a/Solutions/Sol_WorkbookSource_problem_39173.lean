-- Prove2me | solution 1 for WorkbookSource.problem_39173
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:40.454826+00:00
-- url     : https://prove2.me/submissions/f0c0159a-fc11-4276-a257-a3ae83d83157

/- Source: InternLM Lean-Workbook lean_workbook_39173, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (a b : ℤ) (h₁ : 2 < a) (h₂ : 2 < b) : a * b > a + b := by
  nlinarith [mul_nonneg (show 0≤a-3 by omega) (show 0≤b-3 by omega)]

example : (∀ (a b : ℤ) (h₁ : 2 < a) (h₂ : 2 < b), a * b > a + b) := @solution
#print axioms solution
