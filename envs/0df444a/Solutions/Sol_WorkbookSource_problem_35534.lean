-- Prove2me | solution 1 for WorkbookSource.problem_35534
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:54.929284+00:00
-- url     : https://prove2.me/submissions/67c4690a-5873-4623-868b-08b4cdc20b8f

/- InternLM Lean-Workbook, lean_workbook_35534, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (h₁ : π / 2 * 1 = π / 2) : π / 2 * (1 + 1) = π  := by
  first
  | solve
    | ring
  | solve
    | nlinarith [h₁]
  | solve
    | rw [mul_add, h₁, ← mul_one π]
      ring_nf
  | solve
    | rw [mul_add, h₁, add_comm]
      linarith [h₁]
  | solve
    | rw [mul_add, h₁]
      ring
  | solve
    | rw [mul_add]
      linarith
  | solve
    | simp only [mul_add, mul_one, h₁]
      linarith [pi_pos]
  | solve
    | rw [mul_add, h₁]
      simp [mul_one, add_comm]
  | solve
    | linear_combination h₁
  | solve
    | rw [mul_add, h₁]
      field_simp
  | solve
    | linarith only [h₁]
  | solve
    | rw [mul_add, h₁, add_comm]
      ring_nf
  | solve
    | rw [mul_add, mul_one]
      linarith [h₁]
  | solve
    | rw [mul_add, h₁]
      ring_nf
  | solve
    | rw [mul_add, h₁]
      rw [add_comm]
      ring
  | solve
    | rw [mul_add, h₁]
      linarith
  | solve
    | linarith [h₁, h₁]
  | solve
    | rw [add_comm, mul_add, h₁]
      ring_nf
  | solve
    | rw [mul_add, h₁, add_comm]
      ring
  | solve
    | rw [mul_add]
      rw [h₁, ← mul_one π]
      ring
example : (∀ (h₁ : π / 2 * 1 = π / 2), π / 2 * (1 + 1) = π) := @solution
#print axioms solution
