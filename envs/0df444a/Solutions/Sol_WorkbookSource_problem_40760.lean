-- Prove2me | solution 1 for WorkbookSource.problem_40760
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:51.002631+00:00
-- url     : https://prove2.me/submissions/35b31530-e199-4fd0-a6e3-f1e60454ac92

/- InternLM Lean-Workbook, lean_workbook_40760, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : (3 * (x + 2 / 3) ^ 2 + 6 * (y + 1 / 3) ^ 2 + (x - 2 * y) ^ 2) ≥ 0  := by
  first
  | solve
    | positivity
  | solve
    | rw [add_assoc]
      positivity
  | solve
    | linarith [sq_nonneg (x + 2 / 3), sq_nonneg (y + 1 / 3), sq_nonneg (x - 2 * y)]
  | solve
    | norm_num [sq_nonneg, add_nonneg]
  | solve
    | apply_rules [add_nonneg, sq_nonneg, mul_nonneg] <;> nlinarith
  | solve
    | apply add_nonneg <;> nlinarith
  | solve
    | simp [mul_add, add_mul, add_assoc, add_comm, add_left_comm]
      nlinarith
  | solve
    | norm_num
      nlinarith only [sq_nonneg (x + 2 / 3), sq_nonneg (y + 1 / 3)]
  | solve
    | nontriviality ℝ
      positivity
  | solve
    | simp [sub_eq_add_neg]
      positivity
  | solve
    | nlinarith [mul_self_nonneg (x + 2 / 3), mul_self_nonneg (y + 1 / 3), mul_self_nonneg (x - 2 * y)]
  | solve
    | nlinarith only [x, y]
  | solve
    | linarith only [pow_two_nonneg (x + 2 / 3), pow_two_nonneg (y + 1 / 3), pow_two_nonneg (x - 2 * y)]
  | solve
    | simp [sub_eq_add_neg, add_assoc]
      nlinarith
  | solve
    | simp [add_comm, add_left_comm, add_assoc]
      nlinarith [sq_nonneg (x - 2 * y)]
  | solve
    | apply_rules [add_nonneg, sq_nonneg, mul_nonneg] <;> norm_num
  | solve
    | nlinarith [sq_nonneg (x - 2 * y)]
  | solve
    | rw [add_comm]
      simp [add_assoc]
      nlinarith [sq_nonneg (x - 2 * y)]
  | solve
    | nlinarith [mul_self_nonneg (3 : ℝ), mul_self_nonneg (x + 2 / 3), mul_self_nonneg (y + 1 / 3)]
  | solve
    | norm_num
      nlinarith only [sq_nonneg (x + 2 / 3), sq_nonneg (y + 1 / 3), sq_nonneg (x - 2 * y)]
example : (∀ (x y : ℝ), (3 * (x + 2 / 3) ^ 2 + 6 * (y + 1 / 3) ^ 2 + (x - 2 * y) ^ 2) ≥ 0) := @solution
#print axioms solution
