-- Prove2me | solution 1 for WorkbookSource.problem_34657
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:51.850467+00:00
-- url     : https://prove2.me/submissions/a16e062e-146d-4f0d-b540-17c237f62ae1

/- InternLM Lean-Workbook, lean_workbook_34657, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution :
  (2^2020) % 3 = 1  := by
  first
  | solve
    | decide +kernel
  | solve
    | field_simp [pow_mod]
  | solve
    | rw [show 2020 = 2000 + 20 by rfl]
      norm_num [pow_add, pow_succ]
  | solve
    | norm_num [mod_eq_of_lt]
  | solve
    | rw [show (2^2020) = 2^2020 by rfl]
      norm_num
  | solve
    | calc (2^2020) % 3
  | solve
    | norm_num [pow_succ]
  | solve
    | norm_num [Nat.gcd]
  | solve
    | simp [pow_mod]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.mod_eq_of_lt]
  | solve
    | norm_num [Nat.modEq_zero_iff_dvd]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one]
  | solve
    | simp [Nat.mod_eq_of_lt]
  | solve
    | conv => lhs; rw [← Nat.mod_add_div (2 ^ 2020) 3]
  | solve
    | norm_num [Nat.mod_eq_of_lt]
  | solve
    | norm_num [pow_mod]
  | solve
    | convert pow_mod 2 2020 3
  | solve
    | conv => lhs; rw [← Nat.mod_add_div (2^2020) 3]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.mod_self]
  | solve
    | exact pow_mod 2 2020 3
  | solve
    | simp [Nat.pow_mod]
  | solve
    | norm_num [Nat.pow_mod]
  | solve
    | exact (by norm_num : (2^2020) % 3 = 1)
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, pow_two, pow_three]
  | solve
    | norm_num [pow_two]
  | solve
    | simp [Nat.modEq_iff_dvd]
  | solve
    | norm_num [Nat.gcd_rec 2020 3]
  | solve
    | norm_num [Nat.pow_mod, Nat.mod_eq_of_lt]
  | solve
    | norm_num [Nat.gcd_eq_gcd_ab]
  | solve
    | rw [show (2 ^ 2020) % 3 = 1 by norm_num]
  | solve
    | simp [pow_add, pow_mul, pow_one, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  | solve
    | norm_num [pow_succ, Nat.add_mod, Nat.mul_mod]
  | solve
    | norm_num [pow_succ, pow_succ]
example : ((2^2020) % 3 = 1) := @solution
#print axioms solution
