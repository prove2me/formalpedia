-- Prove2me | solution 1 for WorkbookSource.problem_55362
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:59.933099+00:00
-- url     : https://prove2.me/submissions/641ae4e5-1f56-47f9-8f24-9a6b99aea20e

/- Source: InternLM Lean-Workbook lean_workbook_55362, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution : 5 * (137 + 137) ^ 2 + 137 * 137 ≡ 0 [ZMOD 411] := by
  norm_num [Int.ModEq]

example : (5 * (137 + 137) ^ 2 + 137 * 137 ≡ 0 [ZMOD 411]) := @solution
#print axioms solution
