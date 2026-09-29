-- Prove2me | solution 1 for WorkbookSource.problem_40670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:50.423183+00:00
-- url     : https://prove2.me/submissions/46737b65-198a-47e3-a106-76b6aab39969

/- InternLM Lean-Workbook, lean_workbook_40670, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution :
  (2^20) % 7 = 4  := by
  first
  | solve
    | decide +kernel
  | solve
    | convert pow_mod 2 20 7
  | solve
    | exact (by decide : (2 ^ 20) % 7 = 4)
  | solve
    | norm_num [pow_succ, pow_succ]
  | solve
    | exact (by norm_num : 2^20 % 7 = 4)
  | solve
    | simp [Nat.pow_dvd_pow_iff]
  | solve
    | exact Nat.pow_mod _ _ _
  | solve
    | simp [Nat.modEq_iff_dvd]
  | solve
    | simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt]
  | solve
    | norm_num [Nat.pow_mod]
  | solve
    | simp only [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mod_self]
  | solve
    | norm_num [Nat.gcd_eq_gcd_ab 7 4]
  | solve
    | refine' Eq.symm _
      congr
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, pow_two, pow_three]
  | solve
    | simp only [Nat.pow_mod, Nat.mod_mod]
  | solve
    | norm_num [Nat.pow]
  | solve
    | conv => lhs; rw [← Nat.mod_add_div 2 7]
  | solve
    | norm_num [Nat.mod_eq_of_lt]
  | solve
    | norm_num [pow_succ, pow_zero]
  | solve
    | calc (2 ^ 20) % 7
  | solve
    | conv => lhs; rw [← Nat.mod_add_div (2 ^ 20) 7]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one]
  | solve
    | norm_num [pow_succ]
  | solve
    | exact (by norm_num : 2 ^ 20 % 7 = 4)
  | solve
    | exact (rfl : (2^20) % 7 = 4)
  | solve
    | simp only [Nat.pow_succ, Nat.pow_zero, Nat.mod_eq_of_lt]
  | solve
    | simp [Nat.pow_succ]
  | solve
    | simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mod_self]
  | solve
    | simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt]
  | solve
    | simp only [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
  | solve
    | simp only [Nat.pow_zero, Nat.pow_succ]
  | solve
    | rw [show (2 ^ 20) = 1048576 by norm_num, show 1048576 % 7 = 4 by norm_num]
  | solve
    | norm_num [pow_two]
example : ((2^20) % 7 = 4) := @solution
#print axioms solution
