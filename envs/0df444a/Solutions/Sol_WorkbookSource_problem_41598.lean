-- Prove2me | solution 1 for WorkbookSource.problem_41598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:54.654127+00:00
-- url     : https://prove2.me/submissions/f17b87c0-eda3-40bf-873c-d3eff8c20d83

/- InternLM Lean-Workbook, lean_workbook_41598, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) : 2 * (1 - 2 * Real.sin x ^ 2) + 2 * Real.sin x = 9 / 4 - 4 * (Real.sin x - 1 / 4) ^ 2  := by
  first
  | solve
    | ring
  | solve
    | simp [sub_sq, mul_add, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | simp [mul_sub, sub_mul, mul_comm, mul_assoc, mul_left_comm]
      ring
  | solve
    | field_simp [sq]
      ring
  | solve
    | simp only [sub_eq_add_neg, mul_add, mul_neg]
      ring_nf
  | solve
    | simp [sq, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, add_assoc]
      ring_nf
  | solve
    | simp [mul_sub, mul_add, sub_add]
      ring_nf
  | solve
    | simp [sub_mul, sub_add]
      ring_nf
  | solve
    | simp [pow_two]
      ring
  | solve
    | field_simp [sub_eq_add_neg]
      ring
  | solve
    | simp [sub_eq_add_neg, add_comm, add_left_comm]
      ring
  | solve
    | simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | simp [sub_mul, mul_sub, mul_add, add_mul, add_assoc, add_comm, add_left_comm]
      ring
  | solve
    | rw [sub_sq]
      ring
  | solve
    | simp [sub_sq]
      ring
  | solve
    | field_simp [Real.sin_sq_add_cos_sq]
      ring
  | solve
    | linear_combination 2 * (1 - 2 * Real.sin x ^ 2) + 2 * Real.sin x - (9 / 4 - 4 * (Real.sin x - 1 / 4) ^ 2)
  | solve
    | field_simp [add_comm]
      ring_nf
  | solve
    | field_simp [Real.sin_sq_add_cos_sq x]
      ring
  | solve
    | linarith only [Real.sin_sq_add_cos_sq x]
  | solve
    | field_simp [pow_two]
      ring_nf
  | solve
    | have h : ∀ x : ℝ, 2 * (1 - 2 * x ^ 2) + 2 * x = 9 / 4 - 4 * (x - 1 / 4) ^ 2 := by intros; ring
      exact h (Real.sin x)
example : (∀ (x : ℝ), 2 * (1 - 2 * Real.sin x ^ 2) + 2 * Real.sin x = 9 / 4 - 4 * (Real.sin x - 1 / 4) ^ 2) := @solution
#print axioms solution
