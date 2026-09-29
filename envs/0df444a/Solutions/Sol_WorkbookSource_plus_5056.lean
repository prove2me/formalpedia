-- Prove2me | solution 1 for WorkbookSource.plus_5056
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:06.309659+00:00
-- url     : https://prove2.me/submissions/d645ce43-b1e2-4512-94ea-21f434c712ac

/- Source: InternLM Lean-Workbook lean_workbook_plus_5056, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a b c : ℝ) (h : 3 = a ^ 2 + b ^ 2 + c ^ 2) : a * b + c ≤ 2 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (c-1)]

example : (∀ (a b c : ℝ) (h : 3 = a ^ 2 + b ^ 2 + c ^ 2), a * b + c ≤ 2) := @solution
#print axioms solution
