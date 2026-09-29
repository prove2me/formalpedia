-- Prove2me | solution 1 for WorkbookSource.problem_53845
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:58.157209+00:00
-- url     : https://prove2.me/submissions/f0d0576e-917a-42bc-a27b-decc13290751

/- Source: InternLM Lean-Workbook lean_workbook_53845, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution : (15:ℝ)^16 > 16^15 := by
  norm_num

example : ((15:ℝ)^16 > 16^15) := @solution
#print axioms solution
