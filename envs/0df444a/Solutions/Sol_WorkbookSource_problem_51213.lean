-- Prove2me | solution 1 for WorkbookSource.problem_51213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:38.12169+00:00
-- url     : https://prove2.me/submissions/6ba8aa7f-b215-4430-969a-dbf4fac0f884

/- Source: InternLM Lean-Workbook, record lean_workbook_51213.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) : a ^ 2 + 4 * b ^ 2 + 8 * c ^ 2 ≥ 3 * a * b + 4 * b * c + 2 * a * c := by
  first
  | solve
    | simp [add_assoc]
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c)]
  | solve
    | simp only [pow_two]
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c)]
  | solve
    | simp [mul_comm, mul_assoc, mul_left_comm]
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c)]
  | solve
    | simp [sq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c)]

example : (∀ (a b c : ℝ), a ^ 2 + 4 * b ^ 2 + 8 * c ^ 2 ≥ 3 * a * b + 4 * b * c + 2 * a * c) := @solution
#print axioms solution
