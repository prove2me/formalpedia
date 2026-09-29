-- Prove2me | solution 1 for WorkbookSource.problem_16562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:04.181458+00:00
-- url     : https://prove2.me/submissions/856c4f04-423b-4e7b-a67d-0d0e327ec9e8

/- Source: InternLM Lean-Workbook lean_workbook_16562, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 3000
theorem solution : (-5 : ℤ) ^ 2011 + 3 ^ 2011 + 2 ^ 2011 ≡ 0 [ZMOD 2011] := by
  norm_num [Int.ModEq]

example : ((-5 : ℤ) ^ 2011 + 3 ^ 2011 + 2 ^ 2011 ≡ 0 [ZMOD 2011]) := @solution
#print axioms solution
