-- Prove2me | solution 1 for WorkbookSource.problem_34538
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:51.214756+00:00
-- url     : https://prove2.me/submissions/4fc1f885-eaa1-4af0-b4ad-00f375545e8e

/- InternLM Lean-Workbook, lean_workbook_34538, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 - a * b + b^2 - (a + b) / 2)^2 + (b^2 - b * c + c^2 - (b + c) / 2)^2 + (c^2 - c * a + a^2 - (c + a) / 2)^2 ≥ 0  := by
  first
  | solve
    | positivity
  | solve
    | linarith [pow_two_nonneg (a^2 - a * b + b^2 - (a + b) / 2), pow_two_nonneg (b^2 - b * c + c^2 - (b + c) / 2), pow_two_nonneg (c^2 - c * a + a^2 - (c + a) / 2)]
  | solve
    | apply_rules [add_nonneg, pow_two_nonneg, sub_nonneg]
  | solve
    | simp only [add_comm, add_left_comm, mul_comm, mul_left_comm]
      positivity
  | solve
    | apply_rules [add_nonneg, pow_two_nonneg]
  | solve
    | apply_rules [sq_nonneg, add_nonneg, mul_nonneg]
  | solve
    | apply_rules [add_nonneg, sq_nonneg, sub_nonneg]
  | solve
    | apply_rules [sq_nonneg, add_nonneg]
  | solve
    | apply_rules [add_nonneg] <;> apply sq_nonneg
  | solve
    | simp only [add_comm, add_left_comm]
      positivity
  | solve
    | nontriviality ℝ
      positivity
example : (∀ (a b c : ℝ), (a^2 - a * b + b^2 - (a + b) / 2)^2 + (b^2 - b * c + c^2 - (b + c) / 2)^2 + (c^2 - c * a + a^2 - (c + a) / 2)^2 ≥ 0) := @solution
#print axioms solution
