-- Prove2me | solution 1 for WorkbookSource.problem_33828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:48.58577+00:00
-- url     : https://prove2.me/submissions/3c2d0dc8-d4d0-4802-aa82-acea79878ad8

/- InternLM Lean-Workbook, lean_workbook_33828, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : (2^(33)*3^(10) : ℝ) > 5^(21)  := by
  first
  | solve
    | norm_num
  | solve
    | norm_num [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
  | solve
    | norm_num [show (2:ℝ)^3 = 8 by norm_num, show (5:ℝ)^2 = 25 by norm_num]
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, mul_comm]
  | solve
    | exact (by norm_num : (2:ℝ) ^ 33 * 3 ^ 10 > 5 ^ 21)
  | solve
    | norm_num [show (2 : ℝ) = (2 : ℕ) by norm_cast, show (5 : ℝ) = (5 : ℕ) by norm_cast]
  | solve
    | ring_nf
      norm_num [pow_pos, mul_pos]
  | solve
    | rw [show (2 : ℝ) = (2 : ℚ) by norm_num, show (3 : ℝ) = (3 : ℚ) by norm_num, show (5 : ℝ) = (5 : ℚ) by norm_num]
      norm_num
  | solve
    | repeat norm_num
  | solve
    | norm_num [show (2 : ℝ) = (2 : ℕ) by norm_cast, show (3 : ℝ) = (3 : ℕ) by norm_cast]
  | solve
    | norm_num [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) 33, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) 10, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5) 21]
  | solve
    | norm_num [Set.mem_setOf_eq]
  | solve
    | norm_num only [show (2:ℝ) = (2:ℚ) by norm_cast, show (3:ℝ) = (3:ℚ) by norm_cast, show (5:ℝ) = (5:ℚ) by norm_cast]
  | solve
    | norm_num [show (2:ℝ)^3 = 8 by norm_num, show (3:ℝ)^2 = 9 by norm_num]
  | solve
    | norm_num [pow_one, pow_one, pow_one]
  | solve
    | norm_num [show (2 : ℝ) ^ 3 = 8 by norm_num, show (3 : ℝ) ^ 2 = 9 by norm_num]
  | solve
    | norm_num [pow_succ, pow_succ]
  | solve
    | norm_num [pow_succ, pow_mul]
  | solve
    | norm_num [Nat.gcd]
  | solve
    | norm_num [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]
  | solve
    | norm_num [Real.rpow_def_of_pos]
  | solve
    | norm_num [pow_succ, pow_mul, mul_pow]
  | solve
    | norm_num [show (2 : ℝ) = (2 : ℚ) by norm_cast, show (3 : ℝ) = (3 : ℚ) by norm_cast]
  | solve
    | ring_nf
      norm_num [pow_succ]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_succ]
  | solve
    | norm_num [show 2 ^ 3 = 8 by norm_num, show 3 ^ 2 = 9 by norm_num]
  | solve
    | norm_num [pow_succ, pow_zero]
  | solve
    | linarith [show (2:ℝ)^(33) * 3^(10) > 5^(21) by norm_num]
  | solve
    | norm_num [mul_pow, pow_add]
  | solve
    | ring_nf
      norm_num [pow_zero]
  | solve
    | norm_num [pow_succ, pow_zero, pow_one]
  | solve
    | norm_num [show (2:ℝ) = 2 by rfl, show (3:ℝ) = 3 by rfl, show (5:ℝ) = 5 by rfl]
  | solve
    | norm_num [show (2 : ℝ) = (2 : ℚ) by norm_cast, show (3 : ℝ) = (3 : ℚ) by norm_cast, show (5 : ℝ) = (5 : ℚ) by norm_cast]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, mul_one]
  | solve
    | norm_num [pow_one]
  | solve
    | norm_num [pow_one, pow_succ]
  | solve
    | rw [show (2 ^ 33 * 3 ^ 10 : ℝ) = (2 ^ 33 * 3 ^ 10 : ℕ) by norm_num, show (5 ^ 21 : ℝ) = (5 ^ 21 : ℕ) by norm_num]
      norm_num
  | solve
    | norm_num [pow_add, pow_one, mul_comm]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero]
  | solve
    | norm_num [pow_succ]
  | solve
    | norm_num [←pow_mul, ←pow_add]
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, mul_comm, mul_assoc, mul_left_comm]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one, mul_assoc]
  | solve
    | norm_num [pow_one, pow_two]
  | solve
    | norm_num only [pow_succ, pow_zero, pow_one]
  | solve
    | norm_num [pow_succ, pow_one, pow_zero, mul_one, mul_zero, mul_two]
  | solve
    | norm_num at *
  | solve
    | norm_num [show 5 ^ 21 < 2 ^ 33 * 3 ^ 10 by norm_num]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one]
  | solve
    | norm_num [pow_mul]
  | solve
    | norm_num [pow_succ, pow_zero, mul_one]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one, pow_succ, pow_one]
  | solve
    | norm_num [pow_two, pow_three]
  | solve
    | norm_num [show (3:ℝ) = 3 from rfl]
  | solve
    | norm_num [show (2:ℝ)^(33) * 3^(10) > 5^(21) by norm_num]
  | solve
    | norm_num [show 125 < 3^5 by norm_num, show 16807 < 5^7 by norm_num]
  | solve
    | rw [show (2 : ℝ) = (2 : ℚ) by norm_cast, show (3 : ℝ) = (3 : ℚ) by norm_cast, show (5 : ℝ) = (5 : ℚ) by norm_cast]
      norm_num [pow_succ, pow_zero]
  | solve
    | norm_num [Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_one, Nat.mul_comm]
  | solve
    | norm_num [pow_succ, pow_zero, pow_one, mul_one, mul_comm, mul_assoc]
  | solve
    | norm_num [pow_succ, pow_mul, pow_one]
  | solve
    | norm_num [pow_succ, pow_succ, pow_succ]
example : ((2^(33)*3^(10) : ℝ) > 5^(21)) := @solution
#print axioms solution
