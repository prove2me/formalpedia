-- Prove2me | solution 1 for WorkbookSource.problem_35023
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:54.183874+00:00
-- url     : https://prove2.me/submissions/a67d23ba-923f-4fdf-97bd-554bab14dc2a

/- InternLM Lean-Workbook, lean_workbook_35023, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (h : a = 2/3 ∧ b = 1/3 ∧ c = 0) : a^2 * b + b^2 * c + c^2 * a = 4/27  := by
  first
  | solve
    | rcases h with ⟨rfl,rfl,rfl⟩
      norm_num
  | solve
    | ring_nf at h ⊢
      norm_num [h.1, h.2.1, h.2.2]
  | solve
    | field_simp [h.1, h.2.1, h.2.2, mul_comm, mul_assoc, mul_left_comm]
      ring_nf
  | solve
    | field_simp [h]
      norm_num
  | solve
    | simp [h.1, h.2.1, h.2.2]
      norm_num [h.1, h.2.1, h.2.2]
  | solve
    | simp only [h]
      norm_num [h.1, h.2.1, h.2.2]
  | solve
    | rw [h.left, h.right.left, h.right.right]
      linarith [h.left, h.right.left, h.right.right]
  | solve
    | simp [h]
      norm_num [h]
  | solve
    | simp [h.1, h.2.1, h.2.2, mul_comm, mul_assoc, mul_left_comm]
      norm_num [h]
  | solve
    | simp [h.1, h.2]
      norm_num [h.1, h.2]
  | solve
    | field_simp [h.1, h.2.1, h.2.2, mul_comm, mul_assoc, mul_left_comm]
      linarith [h.1, h.2.1, h.2.2]
  | solve
    | rw [h.1, h.2.1, h.2.2]
      norm_num
  | solve
    | field_simp [h.1, h.2]
      linarith
  | solve
    | simp only [h]
      ring
  | solve
    | simp [h, mul_zero, add_zero, sq]
      ring_nf
  | solve
    | eta_reduce at h
      rw [h.1, h.2.1, h.2.2]
      norm_num [h]
  | solve
    | rw [h.left, h.right.left, h.right.right]
      norm_num at h ⊢
  | solve
    | rcases h with ⟨rfl, rfl, rfl⟩
      norm_num [div_eq_mul_inv, inv_eq_one_div]
  | solve
    | norm_num [h.1, h.2.1, h.2.2]
  | solve
    | simp [h, mul_comm, mul_assoc, mul_left_comm]
      norm_num [h.1, h.2.1, h.2.2]
  | solve
    | simp [h.1, h.2]
      norm_num
  | solve
    | simp [h, pow_two]
      norm_num [h]
  | solve
    | simp only [h.1, h.2.1, h.2.2, zero_mul, mul_zero, add_zero]
      ring
  | solve
    | have h1 : a = 2/3 := h.1
      have h2 : b = 1/3 := h.2.1
      have h3 : c = 0 := h.2.2
      field_simp [h1, h2, h3]
      norm_num [h1, h2, h3]
  | solve
    | simp only [h.1, h.2.1, h.2.2]
      norm_num
  | solve
    | rw [h.1, h.2.1, h.2.2]
      norm_num [h]
  | solve
    | rw [h.1, h.2.1, h.2.2]
      ring_nf
  | solve
    | field_simp [h.1, h.2.1, h.2.2]
      linarith
  | solve
    | simp only [h.left, h.right.left, h.right.right]
      ring
  | solve
    | rw [h.left, h.right.left, h.right.right]
      norm_num
  | solve
    | simp only [h.1, h.2.1, h.2.2]
      ring
  | solve
    | field_simp [h.1, h.2.1, h.2.2]
      norm_num [h]
  | solve
    | field_simp [h]
      linarith
  | solve
    | field_simp [h.1, h.2]
      ring_nf
  | solve
    | rw [h.1, h.2.1, h.2.2]
      norm_num at h ⊢
  | solve
    | rcases h with ⟨rfl, rfl, rfl⟩
      norm_num [div_eq_mul_inv]
example : (∀ (a b c : ℝ) (h : a = 2/3 ∧ b = 1/3 ∧ c = 0), a^2 * b + b^2 * c + c^2 * a = 4/27) := @solution
#print axioms solution
