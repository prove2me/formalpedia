-- Prove2me | solution 1 for WorkbookSource.problem_40520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:47.655216+00:00
-- url     : https://prove2.me/submissions/d51defb8-4b8a-40d2-91f8-47ceb5876e0d

/- InternLM Lean-Workbook, lean_workbook_40520, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) (hx : x = 90) : (2 * x - 4 + x) / (23 * x + 2) = 19 / 148  := by
  first
  | solve
    | norm_num [hx]
  | solve
    | simp only [hx, div_eq_mul_inv]
      ring
  | solve
    | simp [hx]
      norm_num
  | solve
    | simp [hx]
      norm_num [hx]
  | solve
    | rw [hx]
      norm_num [hx, mul_comm, mul_assoc, mul_left_comm]
  | solve
    | rw [hx, mul_comm]
      norm_num [hx, mul_comm]
  | solve
    | rw [hx, mul_comm]
      norm_num [hx]
  | solve
    | simp only [hx]
      norm_num [hx]
  | solve
    | simp only [hx, mul_one]
      norm_num
  | solve
    | rw [hx]
      ring
  | solve
    | field_simp [hx, show (2 : ℝ) ≠ 0 by norm_num, show (23 : ℝ) ≠ 0 by norm_num]
      ring
  | solve
    | simp [hx, div_eq_mul_inv]
      ring
  | solve
    | rw [hx, div_eq_mul_inv]
      norm_num [div_eq_mul_inv]
  | solve
    | simp [hx, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      ring
  | solve
    | field_simp [hx]
      norm_num
  | solve
    | rw [hx, div_eq_mul_inv]
      norm_num [hx]
  | solve
    | field_simp [hx, mul_comm]
      ring
  | solve
    | rw [hx]
      norm_num [mul_comm, mul_assoc, mul_left_comm]
  | solve
    | field_simp [hx]
      norm_num [hx]
  | solve
    | field_simp [hx, mul_comm]
      norm_num [hx, mul_comm, mul_assoc, mul_left_comm]
  | solve
    | field_simp [hx, mul_assoc]
      ring
  | solve
    | rw [hx] at *
      norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  | solve
    | subst hx
      norm_num [div_eq_mul_inv, mul_assoc]
  | solve
    | subst hx
      ring
  | solve
    | rw [hx]
      norm_num [hx]
  | solve
    | simp only [hx, Nat.cast_ofNat]
      norm_num [hx]
  | solve
    | field_simp [hx, show (23 : ℝ) ≠ 0 by norm_num, show (148 : ℝ) ≠ 0 by norm_num]
      ring
  | solve
    | field_simp [hx]
      linarith [hx]
  | solve
    | rw [hx]
      norm_num [Nat.cast_ofNat]
  | solve
    | rw [hx]
      norm_num [Nat.div_eq_of_eq_mul_left, Nat.div_eq_of_eq_mul_left]
  | solve
    | rw [hx] at *
      norm_num [hx]
example : (∀ (x : ℝ) (hx : x = 90), (2 * x - 4 + x) / (23 * x + 2) = 19 / 148) := @solution
#print axioms solution
