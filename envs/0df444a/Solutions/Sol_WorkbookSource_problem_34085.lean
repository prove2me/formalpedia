-- Prove2me | solution 1 for WorkbookSource.problem_34085
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:49.48487+00:00
-- url     : https://prove2.me/submissions/031bed6a-ba17-46c5-80f4-f362b494c0ee

/- InternLM Lean-Workbook, lean_workbook_34085, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : 2^16 + 1 ≡ 65537 [MOD 2^31 - 1]  := by
  first
  | solve
    | decide +kernel
  | solve
    | norm_num [Nat.modEq_iff_dvd, Nat.ModEq]
  | solve
    | norm_num [pow_succ, pow_one, Nat.ModEq]
  | solve
    | norm_num [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd]
  | solve
    | conv => lhs; rw [← pow_one 2]
  | solve
    | conv => lhs; rw [← Nat.mod_add_div (2^16) (2^31 - 1)]
  | solve
    | rw [ModEq]
      norm_num
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, Nat.ModEq]
  | solve
    | conv_lhs => norm_num [pow_succ, pow_zero]
  | solve
    | change 2^16 + 1 % (2^31 - 1) = 65537 % (2^31 - 1)
      norm_num
  | solve
    | conv => lhs; rw [← Nat.mod_add_div 2 31]
  | solve
    | norm_num [pow_one, pow_succ, pow_succ, pow_succ]
      decide
  | solve
    | conv_lhs => rw [← Nat.mod_add_div (2 ^ 16) (2 ^ 31)]
  | solve
    | simp only [Nat.ModEq]
      norm_num
  | solve
    | conv => lhs; rw [← pow_one 2]; norm_num [pow_succ]
  | solve
    | norm_num [Nat.modEq_of_dvd]
  | solve
    | conv_lhs => norm_num [pow_one]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one, Nat.ModEq]
  | solve
    | conv => lhs; rw [← Nat.mod_add_div (2^16 + 1) (2^31 - 1)]
  | solve
    | norm_num [Nat.ModEq, Nat.pow_mod]
  | solve
    | simp [Nat.ModEq]
  | solve
    | exact (show 2^16 + 1 % (2^31 - 1) = 65537 from by norm_num)
example : (2^16 + 1 ≡ 65537 [MOD 2^31 - 1]) := @solution
#print axioms solution
