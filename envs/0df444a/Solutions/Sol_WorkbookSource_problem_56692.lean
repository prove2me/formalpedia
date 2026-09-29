-- Prove2me | solution 1 for WorkbookSource.problem_56692
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:02.936663+00:00
-- url     : https://prove2.me/submissions/1426563f-5371-4421-b4d1-a9be9a251a90

/- Source: InternLM Lean-Workbook lean_workbook_56692, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution : 3! * 4 * 5 / 2 - 1 = 59 := by
  norm_num [Nat.factorial]

example : (3! * 4 * 5 / 2 - 1 = 59) := @solution
#print axioms solution
