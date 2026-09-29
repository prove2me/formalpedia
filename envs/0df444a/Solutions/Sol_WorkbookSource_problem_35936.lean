-- Prove2me | solution 1 for WorkbookSource.problem_35936
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:58.080914+00:00
-- url     : https://prove2.me/submissions/d1136c5e-5122-44e5-a4be-9560282318b5

/- InternLM Lean-Workbook, lean_workbook_35936, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (b h : ℝ) : (1 / 2 * (11 / 10 * b) * (9 / 10 * h) : ℝ) = 99 / 200 * (b * h)  := by
  first
  | solve
    | ring
  | solve
    | norm_num [mul_assoc]
      ring
  | solve
    | norm_num [mul_comm, mul_assoc, mul_left_comm]
  | solve
    | norm_num [div_eq_mul_one_div]; ring
  | solve
    | rw [mul_comm b h]
      ring_nf
  | solve
    | simp [mul_assoc]
      ring_nf
  | solve
    | field_simp [mul_comm]
      ring_nf
  | solve
    | simp [div_eq_mul_inv]
      ring_nf
  | solve
    | norm_num [div_eq_mul_inv, inv_mul_cancel]
      ring
  | solve
    | norm_num [mul_assoc, mul_comm, mul_left_comm]
  | solve
    | linear_combination 99 / 200 * (b * h) - 1 / 2 * (11 / 10 * b) * (9 / 10 * h)
  | solve
    | linarith [h, b]
  | solve
    | norm_num [mul_assoc]; ring
  | solve
    | norm_num at *
      ring
  | solve
    | field_simp [show (2 : ℝ) ≠ 0 by norm_num, show (10 : ℝ) ≠ 0 by norm_num]
      ring
  | solve
    | nlinarith only [b, h]
  | solve
    | norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  | solve
    | field_simp [show (2 : ℝ) ≠ 0 by norm_num, show (10 : ℝ) ≠ 0 by norm_num]; ring
  | solve
    | simp only [mul_assoc]
      ring_nf
  | solve
    | linear_combination 11 / 20 * b * 9 / 10 * h
  | solve
    | linear_combination 11 / 20 * 9 / 10 * (b * h) - 1 / 2 * 11 / 10 * 9 / 10 * (b * h)
  | solve
    | linear_combination 11 / 20 * b * 9 / 10 * h - 99 / 200 * (b * h)
  | solve
    | norm_num [div_eq_mul_inv, mul_assoc]
      ring_nf
  | solve
    | ring_nf at h ⊢
  | solve
    | field_simp [show (200 : ℝ) ≠ 0 by norm_num]
      ring_nf
example : (∀ (b h : ℝ), (1 / 2 * (11 / 10 * b) * (9 / 10 * h) : ℝ) = 99 / 200 * (b * h)) := @solution
#print axioms solution
