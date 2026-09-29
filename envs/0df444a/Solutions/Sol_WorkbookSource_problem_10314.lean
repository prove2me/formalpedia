-- Prove2me | solution 1 for WorkbookSource.problem_10314
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:01.023837+00:00
-- url     : https://prove2.me/submissions/e7bf15dc-7fc0-4bfd-92d3-d3af16748da5

/- Source: InternLM Lean-Workbook lean_workbook_10314, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (n : ℕ) : 3^n ≥ 2*n + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

example : (∀ (n : ℕ), 3^n ≥ 2*n + 1) := @solution
#print axioms solution
