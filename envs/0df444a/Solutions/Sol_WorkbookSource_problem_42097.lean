-- Prove2me | solution 1 for WorkbookSource.problem_42097
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:55.333133+00:00
-- url     : https://prove2.me/submissions/85b7971e-7494-48ae-8855-b0431406c517

/- InternLM Lean-Workbook, lean_workbook_42097, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 + a * b * (a + b) + b * c * (b + c) + c * a * (c + a) = (a^2 + b^2 + c^2) * (a + b + c)  := by
  first
  | solve
    | ring
  | solve
    | simp [sq, mul_add, add_mul]
      ring
  | solve
    | simp [mul_add, mul_comm, mul_left_comm]
      ring
  | solve
    | simp [mul_add, add_mul, pow_two, pow_three]
      ring
  | solve
    | linarith [sq a, sq b, sq c]
  | solve
    | field_simp [add_assoc]
      ring
  | solve
    | nlinarith [sq a, sq b, sq c]
  | solve
    | simp [add_mul]
      ring
  | solve
    | rw [add_mul]
      ring
  | solve
    | simp only [add_mul, mul_add]
      ring
  | solve
    | simp only [mul_add, mul_comm, mul_left_comm]
      ring
  | solve
    | simp [sq, add_mul, mul_add]
      ring
  | solve
    | simp [left_distrib, right_distrib, mul_assoc, mul_comm, mul_left_comm]
      ring
  | solve
    | field_simp [mul_add, add_mul, mul_comm, mul_left_comm]
      ring
  | solve
    | simp [sq]
      ring
  | solve
    | field_simp [add_comm]
      ring
  | solve
    | simp only [mul_add, add_mul, mul_comm, mul_left_comm]
      ring
  | solve
    | field_simp [mul_add, add_mul]; ring
  | solve
    | field_simp [add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | simp only [add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | field_simp [mul_assoc]
      ring_nf
  | solve
    | simp only [add_comm]
      ring
  | solve
    | field_simp [mul_add, add_mul, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | simp [add_mul, mul_add, mul_comm, mul_left_comm, sq]
      ring_nf
  | solve
    | rw [add_comm]
      ring_nf
  | solve
    | simp only [mul_add, add_mul, mul_comm, mul_left_comm, pow_two, pow_one]
      ring
  | solve
    | simp [add_comm]
      ring
example : (∀ (a b c : ℝ), a^3 + b^3 + c^3 + a * b * (a + b) + b * c * (b + c) + c * a * (c + a) = (a^2 + b^2 + c^2) * (a + b + c)) := @solution
#print axioms solution
