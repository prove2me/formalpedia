-- Prove2me | solution 1 for WorkbookSource.problem_39057
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:43.691274+00:00
-- url     : https://prove2.me/submissions/cbd5b1a6-7a8e-4f06-a677-f9f598e74450

/- InternLM Lean-Workbook, lean_workbook_39057, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : ¬(5 ∣ (2^29 + 2^15 + 1))  := by
  first
  | solve
    | decide +kernel
  | solve
    | norm_num [Nat.gcd_eq_gcd_ab 5 29]
  | solve
    | simp only [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
      decide
  | solve
    | norm_num [pow_succ, pow_mul]
  | solve
    | rw [Nat.dvd_iff_mod_eq_zero]
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  | solve
    | norm_num [pow_add, pow_one, pow_two, pow_succ]
  | solve
    | norm_num [pow_succ, pow_succ, pow_one]
  | solve
    | norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
  | solve
    | simp only [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod, Nat.mod_eq_zero_of_dvd]
      decide
  | solve
    | simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
      decide
  | solve
    | norm_num [Nat.dvd_add, Nat.dvd_add]
  | solve
    | simp only [Nat.dvd_iff_mod_eq_zero]
      norm_num
  | solve
    | norm_num [Nat.gcd]
  | solve
    | simp [Nat.dvd_add_iff_right]
      norm_num
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | solve
    | rw [Nat.dvd_iff_mod_eq_zero]
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
  | solve
    | norm_num [pow_one, pow_succ]
  | solve
    | norm_num [pow_succ, pow_zero]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero]
  | solve
    | simp only [Nat.dvd_iff_mod_eq_zero, Nat.pow_succ, Nat.add_mod, Nat.mul_mod, Nat.pow_zero,
        Nat.mod_mod]
      norm_num
  | solve
    | norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_succ, Nat.add_mod]
  | solve
    | simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  | solve
    | norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  | solve
    | simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
  | solve
    | norm_num [Nat.div_eq_of_eq_mul_left, Nat.mod_eq_of_lt]
  | solve
    | rw [← Nat.mod_add_div (2 ^ 29 + 2 ^ 15 + 1) 5]
      norm_num [Nat.mod_eq_of_lt]
  | solve
    | norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
example : (¬(5 ∣ (2^29 + 2^15 + 1))) := @solution
#print axioms solution
