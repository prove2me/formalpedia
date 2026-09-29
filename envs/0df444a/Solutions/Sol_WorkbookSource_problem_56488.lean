-- Prove2me | solution 1 for WorkbookSource.problem_56488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:02.29401+00:00
-- url     : https://prove2.me/submissions/3f363120-f2fe-4678-b79d-0583e88b4bd8

/- Source: InternLM Lean-Workbook lean_workbook_56488, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution : (50^100) > 100! := by
  norm_num [Nat.factorial]

example : ((50^100) > 100!) := @solution
#print axioms solution
