-- Prove2me | solution 1 for WorkbookSource.problem_44189
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:08.762172+00:00
-- url     : https://prove2.me/submissions/2bf5ea60-04ab-4d57-b9c7-5fce366f9fa7

/- InternLM Lean-Workbook, lean_workbook_44189, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (p : ℝ) : p^3 - 8 * p^2 + 15 * p ≤ 0 ↔ p * (p - 3) * (p - 5) ≤ 0  := by
  first
  | solve
    | have : p^3-8*p^2+15*p = p*(p-3)*(p-5) := by ring
      rw [this]
  | solve
    | simp [sq, mul_add, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | simp only [sub_eq_add_neg, mul_add, mul_neg, sub_neg_eq_add]
      ring_nf
  | solve
    | rw [mul_comm]
      ring_nf
  | solve
    | constructor <;> intro h
      nlinarith
      nlinarith only [h]
  | solve
    | field_simp [sub_eq_add_neg, add_assoc]
      ring_nf
  | solve
    | simp only [pow_two, pow_three]
      ring_nf
  | solve
    | simp only [sub_mul, mul_sub, mul_zero, zero_mul, sub_zero, sub_add_sub_cancel, sub_self, zero_add,
        mul_one, true_and]
      ring_nf
  | solve
    | rw [← sub_nonpos]
      ring_nf
  | solve
    | simp only [sub_eq_add_neg, add_assoc, mul_add, add_mul]
      ring_nf
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
  | solve
    | simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, add_mul, mul_add, mul_comm, mul_left_comm]
      ring_nf
  | solve
    | field_simp [sq]
      ring_nf
  | solve
    | field_simp [mul_assoc]
      ring_nf
  | solve
    | constructor <;> intro h <;> nlinarith [h]
  | solve
    | field_simp [pow_two]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, add_assoc]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, ← sub_sub, sub_mul, mul_assoc]
      ring_nf
  | solve
    | simp [sub_eq_add_neg, add_comm, add_left_comm]
      ring_nf
example : (∀ (p : ℝ), p^3 - 8 * p^2 + 15 * p ≤ 0 ↔ p * (p - 3) * (p - 5) ≤ 0) := @solution
#print axioms solution
