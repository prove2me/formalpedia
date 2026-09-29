-- Prove2me | solution 1 for WorkbookSource.problem_44582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:09.433562+00:00
-- url     : https://prove2.me/submissions/ca3c4565-ae35-4518-a50b-2f7cc5800f79

/- InternLM Lean-Workbook, lean_workbook_44582, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) : x^5 - 2 * x^2 - 9 * x - 6 = 0 ↔ (x + 1)^2 * (x - 2) * (x^2 + 3) = 0  := by
  first
  | solve
    | have : x^5-2*x^2-9*x-6 = (x+1)^2*(x-2)*(x^2+3) := by ring
      rw [this]
  | solve
    | simp only [sub_eq_add_neg, add_assoc]
      ring_nf
  | solve
    | simp [mul_add, add_mul, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | simp [add_mul, mul_add, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | rw [← sub_eq_zero]
      ring_nf
  | solve
    | simp only [add_sq, sub_eq_add_neg, mul_add, mul_sub, sub_sub_sub_cancel_right]
      ring_nf
  | solve
    | simp only [add_sq, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | field_simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]
      ring_nf
  | solve
    | simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | constructor
      intro h
      ring_nf at h
      linarith
      intro h
      ring_nf at h
      linarith
  | solve
    | simp only [add_sq, sub_eq_add_neg, mul_add, mul_sub, mul_one, sub_sub_sub_cancel_right]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | refine' ⟨fun h => _, fun h => _⟩
      nlinarith [h]
      nlinarith [h]
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm]
      ring_nf
example : (∀ (x : ℝ), x^5 - 2 * x^2 - 9 * x - 6 = 0 ↔ (x + 1)^2 * (x - 2) * (x^2 + 3) = 0) := @solution
#print axioms solution
