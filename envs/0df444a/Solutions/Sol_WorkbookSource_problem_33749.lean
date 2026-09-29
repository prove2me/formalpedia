-- Prove2me | solution 1 for WorkbookSource.problem_33749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:47.13829+00:00
-- url     : https://prove2.me/submissions/a27fe770-eb98-4654-b1f3-f85a599d7b7e

/- InternLM Lean-Workbook, lean_workbook_33749, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (a b c d : ℝ) :
  (a + b) * (c + d) ≤ 2 * (a * c + b * d) ↔ (a - b) * (c - d) ≥ 0  := by
  first
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | simp [mul_add, add_mul]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | constructor
      intro h
      nlinarith [h]
      intro h
      nlinarith [h]
  | solve
    | ring_nf
      simp [sub_eq_add_neg, mul_add, mul_comm, mul_left_comm]
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      constructor <;> intro h
      linarith
      nlinarith
  | solve
    | constructor
      intro h
      linarith [h]
      intro h
      linarith [h]
  | solve
    | simp only [two_mul]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | symm
      ring_nf
      constructor <;> intro h
      linarith [h]
      nlinarith
  | solve
    | field_simp [sub_mul, mul_sub]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      refine' ⟨fun h => _, fun h => _⟩
      linarith
      nlinarith
  | solve
    | ring_nf
      constructor <;> intro h
      linarith
      linarith [h]
  | solve
    | rw [mul_add, add_mul, add_mul]
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      norm_num
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      simp [sub_eq_add_neg, add_comm]
      constructor <;> intro h <;> linarith
  | solve
    | constructor
      intro h
      nlinarith [h]
      intro h
      nlinarith
  | solve
    | field_simp [sub_eq_add_neg]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | simp [mul_add, add_mul, mul_sub, sub_mul]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | rw [mul_add, add_mul, add_mul]
      constructor
      intro h
      linarith
      intro h
      nlinarith
  | solve
    | field_simp [mul_add, mul_comm, mul_left_comm, add_mul, add_comm, add_left_comm]
      constructor <;> intro h <;> linarith
  | solve
    | simp only [sub_eq_add_neg]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      exact ⟨fun h ↦ by linarith [h], fun h ↦ by linarith [h]⟩
  | solve
    | refine' ⟨fun h => _, fun h => _⟩
      linarith [h]
      linarith
  | solve
    | constructor <;> intro h
      linarith
      nlinarith [h]
  | solve
    | simp [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      constructor <;> intro h <;> linarith [h]
  | solve
    | field_simp [mul_add, mul_comm, mul_left_comm]
      ring_nf
      constructor <;> intro h
      linarith
      nlinarith
  | solve
    | ring_nf
      rw [← sub_nonneg]
      constructor <;> intro h <;> linarith
  | solve
    | simp [mul_add, add_mul, mul_sub, sub_mul]
      ring_nf
      constructor <;> intro h
      linarith only [h]
      linarith only [h]
  | solve
    | field_simp [mul_add, add_mul, mul_comm, mul_left_comm]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | rw [mul_add, add_mul]
      ring_nf
      constructor <;> intro h <;> linarith [h]
  | solve
    | simp [sub_eq_add_neg]
      ring_nf
      constructor <;> intro h
      linarith
      nlinarith
  | solve
    | constructor <;> intro h
      linarith
      linarith
  | solve
    | constructor <;> intro h
      linarith [h]
      linarith [h]
example : (∀ (a b c d : ℝ), (a + b) * (c + d) ≤ 2 * (a * c + b * d) ↔ (a - b) * (c - d) ≥ 0) := @solution
#print axioms solution
