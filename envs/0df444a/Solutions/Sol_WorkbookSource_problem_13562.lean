-- Prove2me | solution 1 for WorkbookSource.problem_13562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:50.3318+00:00
-- url     : https://prove2.me/submissions/77c87e8d-0c75-491d-aedd-62fde1e63525

/- Source: InternLM Lean-Workbook lean_workbook_13562, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem solution : ∑ k ∈ Finset.range 16, choose 46 (3 * k) = 23456248059221 := by
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

example : (∑ k ∈ Finset.range 16, choose 46 (3 * k) = 23456248059221) := @solution
#print axioms solution
