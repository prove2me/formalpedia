-- Prove2me | solution 1 for WorkbookSource.problem_52163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:39.600756+00:00
-- url     : https://prove2.me/submissions/db73108b-bfa7-4443-a332-80b41bcf43bd

/- Source: InternLM Lean-Workbook, record lean_workbook_52163.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b * c + 5 * (a + b + c) ^ 3 ≥ 17 * (a + b) * (b + c) * (c + a) := by
  first
  | solve
    | nlinarith [sq_nonneg (b - a), sq_nonneg (c - b), sq_nonneg (a - c)]
  | solve
    | simp [mul_assoc]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | simp only [add_comm]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | simp [add_comm, add_left_comm]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | simp only [pow_two, pow_three]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | simp [add_mul, mul_add, mul_comm, mul_left_comm]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), a * b * c + 5 * (a + b + c) ^ 3 ≥ 17 * (a + b) * (b + c) * (c + a)) := @solution
#print axioms solution
