-- Prove2me | solution 1 for WorkbookSource.problem_39000
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:42.96797+00:00
-- url     : https://prove2.me/submissions/f762d228-f3f9-4062-a455-e65ccbbbcae1

/- InternLM Lean-Workbook, lean_workbook_39000, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (y z : ℝ)
  (h₀ : (y - 1) * (z - 1) ≥ 0) :
  y * z ≥ y + z - 1  := by
  first
  | solve
    | nlinarith
  | solve
    | apply le_of_sub_nonneg
      linarith [h₀]
  | solve
    | rw [ge_iff_le]
      nlinarith [h₀]
  | solve
    | simp [sub_mul, mul_sub, sub_sub_sub_cancel_left]
      nlinarith
  | solve
    | nlinarith [(le_of_lt (zero_lt_one' ℝ))]
  | solve
    | simp [sub_mul, mul_sub]
      nlinarith [h₀]
  | solve
    | linarith [h₀, h₀]
  | solve
    | rw [ge_iff_le] at h₀ ⊢
      linarith
  | solve
    | rw [(by ring : y * z = (y - 1) * (z - 1) + y + z - 1)]
      linarith [h₀]
  | solve
    | ring_nf at h₀ ⊢
      nlinarith only [h₀]
  | solve
    | field_simp [mul_add, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_left_comm]
      nlinarith [h₀]
  | solve
    | simp [mul_add, add_mul, mul_one, one_mul, sub_mul, sub_add, sub_sub]
      nlinarith
  | solve
    | ring_nf at h₀ ⊢
      linarith
  | solve
    | linarith only [h₀]
  | solve
    | simp [sub_mul, mul_sub, sub_sub_sub_cancel_right, mul_comm, mul_assoc, mul_left_comm]
      nlinarith [h₀]
  | solve
    | simp [mul_add, add_mul, sub_mul, sub_add, sub_sub_eq_add_sub, add_sub_assoc]
      linarith
  | solve
    | simp [mul_add, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_left_comm]
      nlinarith
  | solve
    | simp [mul_add, add_mul, sub_mul, sub_add, sub_sub]
      nlinarith [h₀]
  | solve
    | simp [sub_mul, mul_sub]
      linarith only [h₀]
  | solve
    | simp [sub_mul, mul_sub]
      nlinarith
  | solve
    | ring_nf at h₀ ⊢
      linarith [h₀]
  | solve
    | simp [mul_add, add_mul, add_comm, add_left_comm, sub_eq_add_neg, add_assoc, add_left_comm]
      nlinarith
  | solve
    | simp [mul_add, add_mul, sub_mul, mul_sub]
      nlinarith
  | solve
    | simp [mul_add, add_mul, sub_mul, mul_sub, h₀]
      nlinarith
  | solve
    | rw [ge_iff_le, mul_comm]
      linarith
  | solve
    | simp [sub_mul, mul_sub, sub_add_sub_cancel, mul_one, one_mul, sub_nonneg] at h₀
      linarith
  | solve
    | simp [sub_mul, mul_sub, sub_add_sub_cancel, mul_comm, mul_assoc, mul_left_comm]
      nlinarith
  | solve
    | ring_nf at *
      nlinarith
  | solve
    | simp [mul_add, add_mul, sub_mul, mul_sub, sub_sub_sub_cancel_right]
      nlinarith
  | solve
    | norm_num at h₀ ⊢
      nlinarith
  | solve
    | nlinarith [h₀, h₀]
  | solve
    | rw [mul_comm, add_comm]
      linarith [h₀]
example : (∀ (y z : ℝ)
  (h₀ : (y - 1) * (z - 1) ≥ 0), y * z ≥ y + z - 1) := @solution
#print axioms solution
