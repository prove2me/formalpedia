-- Prove2me | solution 1 for WorkbookSource.problem_40641
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:49.761037+00:00
-- url     : https://prove2.me/submissions/fa0ca675-e74c-475c-970e-862362b892c6

/- InternLM Lean-Workbook, lean_workbook_40641, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : 12 ^ 100 ≡ 6 [ZMOD 10]  := by
  first
  | solve
    | decide +kernel
  | solve
    | norm_num [pow_one, pow_succ]
      decide
  | solve
    | norm_num [pow_one, pow_mod, Int.ModEq]
  | solve
    | rw [Int.ModEq]
      norm_num
  | solve
    | norm_num [pow_one, Int.ModEq]
  | solve
    | simp [Int.ModEq, Int.emod]
  | solve
    | show 12 ^ 100 % 10 = 6 % 10
      norm_num
  | solve
    | norm_num [Int.ModEq, pow_succ, pow_mul]
  | solve
    | norm_num [pow_succ, pow_mul, Int.ModEq]
  | solve
    | norm_num [Int.ModEq, pow_succ]
  | solve
    | simp only [Int.ModEq]
      norm_num
  | solve
    | exact (show 12 ^ 100 % 10 = 6 % 10 by norm_num)
  | solve
    | conv_lhs => norm_num [pow_one]
  | solve
    | simp only [Int.ModEq, Int.emod]
      norm_num
  | solve
    | norm_num [pow_succ, pow_mul, pow_one, Int.ModEq]
  | solve
    | norm_num [Nat.ModEq, Int.ModEq]
  | solve
    | norm_num [Int.ModEq]
  | solve
    | simp only [Int.ModEq, Int.dvd_iff_emod_eq_zero, Int.emod_eq_zero_of_dvd]
      norm_num
example : (12 ^ 100 ≡ 6 [ZMOD 10]) := @solution
#print axioms solution
