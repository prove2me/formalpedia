-- Prove2me | solution 1 for WorkbookSource.problem_41109
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:53.375807+00:00
-- url     : https://prove2.me/submissions/351a50a4-5683-4b4b-9f54-fb2d51fc7af6

/- InternLM Lean-Workbook, lean_workbook_41109, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (p : ℝ) :
  p * 0.9 * 1.2 = p * 1.2 * 0.9  := by
  first
  | solve
    | ring
  | solve
    | repeat' rw [mul_assoc]
      ring
  | solve
    | field_simp [mul_assoc, mul_comm, mul_left_comm]
  | solve
    | linear_combination (p * 1.2) * (0.9 - 0.9)
  | solve
    | simp only [mul_assoc]
      simp [mul_comm, mul_assoc]
  | solve
    | simp [mul_comm, mul_assoc, mul_left_comm]
  | solve
    | rw [mul_comm]
      ring_nf
  | solve
    | simp [mul_assoc, mul_comm, mul_left_comm]
  | solve
    | rw [mul_assoc, mul_comm 0.9, ← mul_assoc, mul_comm p, mul_comm 1.2]
  | solve
    | simp only [mul_assoc, mul_comm]
      ring_nf
  | solve
    | linear_combination p * (0.9 * 1.2 - 1.2 * 0.9)
  | solve
    | nlinarith [p]
  | solve
    | simp only [mul_assoc, mul_comm, mul_left_comm]
  | solve
    | simp only [mul_assoc, mul_comm]
      ring
  | solve
    | simp only [mul_assoc]
      simp [mul_comm]
  | solve
    | ring_nf at p ⊢
  | solve
    | simp [← mul_assoc, mul_comm, mul_left_comm]
  | solve
    | simp [mul_comm, mul_left_comm, mul_assoc, mul_left_comm]
  | solve
    | simp only [mul_comm, mul_assoc, mul_left_comm]
  | solve
    | rw [mul_comm]
      linarith
example : (∀ (p : ℝ), p * 0.9 * 1.2 = p * 1.2 * 0.9) := @solution
#print axioms solution
