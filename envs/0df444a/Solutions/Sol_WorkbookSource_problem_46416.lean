-- Prove2me | solution 1 for WorkbookSource.problem_46416
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:14.157051+00:00
-- url     : https://prove2.me/submissions/8974e927-cd7b-4dd5-9913-4515e819e436

/- InternLM Lean-Workbook, lean_workbook_46416, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a : ℚ) (h : a = 5 / (1 / 2 * 1 / 6)) : a = 60  := by
  first
  | solve
    | norm_num at h ⊢
      exact h
  | solve
    | field_simp at h
      linarith only [h]
  | solve
    | field_simp at h ⊢
      linarith [h]
  | solve
    | norm_num [h]
  | solve
    | rw [h]
      ring
  | solve
    | eta_reduce at *
      rw [h]
      norm_num [div_eq_mul_inv, inv_eq_one_div]
  | solve
    | rw [h]
      norm_num [h]
  | solve
    | rw [h]
      norm_num [div_eq_mul_inv, mul_comm, mul_assoc]
  | solve
    | norm_num [h, show (2 : ℚ) ≠ 0 by norm_num, show (6 : ℚ) ≠ 0 by norm_num, show (1 : ℚ) ≠ 0 by norm_num]
  | solve
    | rw [h]
      norm_num at *
  | solve
    | rw [h]
      norm_num
  | solve
    | field_simp at h
      linarith
  | solve
    | rw [h]
      norm_num [div_eq_mul_inv, ← mul_assoc]
  | solve
    | rw [h]
      ring_nf
  | solve
    | simp [h]
      ring
  | solve
    | field_simp [eq_div_iff_mul_eq (ne_of_gt (show (0 : ℚ) < 6 by norm_num)), mul_comm] at h ⊢
      linarith [h]
  | solve
    | rw [h, div_eq_mul_inv]
      norm_num
  | solve
    | norm_num at h
      exact h
  | solve
    | simp [h]
      ring_nf at h ⊢
  | solve
    | rw [h]
      norm_num at h ⊢
  | solve
    | simp [h]
      norm_num
  | solve
    | simp [h]
      norm_num [h]
  | solve
    | rw [h]
      norm_num [div_eq_mul_inv, mul_assoc]
  | solve
    | rw [h]
      norm_num [div_eq_mul_one_div, mul_one_div]
  | solve
    | field_simp [h]
      norm_num [h]
  | solve
    | field_simp [(by norm_num : (1 : ℚ) ≠ 0), (by norm_num : (2 : ℚ) ≠ 0)] at h ⊢
      linarith
  | solve
    | field_simp at h ⊢
      linarith
  | solve
    | simp only [h, div_eq_mul_inv]
      norm_num
  | solve
    | simp [h, mul_comm]
      norm_num
  | solve
    | rw [h, mul_comm]
      norm_num
  | solve
    | rw [h]
      norm_num [div_eq_mul_inv]
  | solve
    | field_simp [h]
      linarith
  | solve
    | simp at h
      ring_nf at h
      norm_num at h
      exact h
  | solve
    | simp_all [div_one]
      norm_num
  | solve
    | simp [h, mul_comm]
      norm_num at h ⊢
  | solve
    | rw [h, div_eq_mul_inv]
      ring_nf
  | solve
    | field_simp [h]
      norm_num at *
  | solve
    | field_simp at h
      rw [h]
      norm_num
  | solve
    | simp only [h, div_eq_mul_inv]
      ring_nf
  | solve
    | field_simp at h
      linarith [h]
  | solve
    | rw [h, div_eq_mul_inv]
      ring
example : (∀ (a : ℚ) (h : a = 5 / (1 / 2 * 1 / 6)), a = 60) := @solution
#print axioms solution
