-- Prove2me | solution 1 for WorkbookSource.problem_35661
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:55.660299+00:00
-- url     : https://prove2.me/submissions/496f71b5-46a5-429c-bf3e-a5e907f8a827

/- InternLM Lean-Workbook, lean_workbook_35661, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (h : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 ≠ 0) : 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 / (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) = 1120  := by
  first
  | solve
    | norm_num
  | solve
    | simp only [mul_one, mul_zero, add_zero, add_one]
  | solve
    | simp only [add_comm, add_left_comm, add_assoc] at h ⊢
  | solve
    | simp [h, Nat.mul_div_cancel_left]
  | solve
    | simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h ⊢
  | solve
    | norm_num [h, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
  | solve
    | norm_num at h ⊢
  | solve
    | simp only [ne_eq, add_eq_zero_iff, not_and_or] at h
      norm_num [h]
  | solve
    | norm_num [h]
  | solve
    | simp only [mul_one, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
  | solve
    | norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
  | solve
    | simp [Nat.mul_div_cancel_left]
  | solve
    | simp [mul_assoc, mul_comm, mul_left_comm, h]
  | solve
    | ring_nf at h ⊢
example : (∀ (h : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 ≠ 0), 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 / (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) = 1120) := @solution
#print axioms solution
