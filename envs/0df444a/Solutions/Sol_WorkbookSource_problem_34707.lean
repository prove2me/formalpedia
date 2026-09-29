-- Prove2me | solution 1 for WorkbookSource.problem_34707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:52.706983+00:00
-- url     : https://prove2.me/submissions/aa9fe759-6f0a-45ea-b6fe-2a029acb7fcb

/- InternLM Lean-Workbook, lean_workbook_34707, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b : ℝ) : a^2 + b^2 - 4*a - 4*b + 8 ≥ 0  := by
  first
  | solve
    | nlinarith [sq_nonneg (a-2),sq_nonneg (b-2)]
  | solve
    | rw [sq, sq]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | have h₁ : 0 ≤ (a - 2)^2 + (b - 2)^2 := by nlinarith
      linarith
  | solve
    | have h1 : 0 ≤ (a - 2)^2 + (b - 2)^2 := by nlinarith
      linarith
  | solve
    | simp [sq, sub_add_eq_sub_sub, sub_self, zero_sub]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | simp [sq, sub_add_eq_sub_sub_swap, sub_self, zero_sub, sub_neg_eq_add]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | ring_nf
      have h1 := sq_nonneg (a - 2)
      have h2 := sq_nonneg (b - 2)
      linarith
  | solve
    | simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | rw [add_comm]
      field_simp [add_comm]
      ring_nf
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | rw [← zero_add (0 : ℝ)]
      ring_nf
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | simp [sq, sub_eq_add_neg, add_comm]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | simp [sq, sub_eq_add_neg, add_comm, add_left_comm]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | have := pow_two_nonneg (a - 2)
      have := pow_two_nonneg (b - 2)
      linarith
  | solve
    | have h₁ : 0 ≤ (a - 2)^2 + (b - 2)^2 := by nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
      linarith
  | solve
    | ring_nf
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | simp [sq]
      nlinarith [sq_nonneg (a-2), sq_nonneg (b-2)]
  | solve
    | rw [add_comm]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | ring_nf
      have h1 : 0 ≤ (a - 2)^2 + (b - 2)^2 := by positivity
      linarith [h1]
  | solve
    | have h1 := sq_nonneg (a - 2)
      have h2 := sq_nonneg (b - 2)
      linarith
  | solve
    | simp [sub_sq, mul_self_nonneg]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | have h1 := sq_nonneg (a - 2)
      have h2 := sq_nonneg (b - 2)
      linarith [h1, h2]
  | solve
    | simp [sq]
      linarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | ring_nf
      have h1 : 0 ≤ (a - 2)^2 + (b - 2)^2 := by nlinarith
      linarith
  | solve
    | rw [add_comm]
      field_simp [sq]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | simp [sq, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
  | solve
    | field_simp
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
example : (∀ (a b : ℝ), a^2 + b^2 - 4*a - 4*b + 8 ≥ 0) := @solution
#print axioms solution
