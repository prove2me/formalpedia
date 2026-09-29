-- Prove2me | solution 1 for WorkbookSource.problem_34138
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:50.639562+00:00
-- url     : https://prove2.me/submissions/148f6508-0da2-4dfc-bcda-8b1c03f42c39

/- InternLM Lean-Workbook, lean_workbook_34138, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution :
  (5^(2*1) ≡ 25 [ZMOD 100])  := by
  first
  | solve
    | decide +kernel
  | solve
    | simp [ZMod.eq_iff_modEq_nat, Nat.ModEq]
  | solve
    | simp [Nat.ModEq, pow_two]
  | solve
    | simp [Nat.ModEq]
  | solve
    | norm_num [pow_succ, pow_zero, pow_one]
  | solve
    | apply Int.ModEq.refl
  | solve
    | simp only [mul_one, pow_two]
      norm_num
  | solve
    | conv in 25 => rw [← pow_one 25]
  | solve
    | simp [pow_two, pow_mul, Nat.modEq_iff_dvd]
  | solve
    | simp only [Nat.modEq_iff_dvd, pow_mul, pow_two]
      decide
  | solve
    | simp (config := { contextual := true }) [Int.ModEq]
  | solve
    | simp only [mul_one, pow_two]
      decide
  | solve
    | simp [Int.ModEq, Int.ModEq]
  | solve
    | simp [ModEq]
  | solve
    | norm_num [Int.ModEq]
  | solve
    | simp only [Nat.modEq_iff_dvd, pow_mul, pow_one]
      decide
  | solve
    | conv_lhs => rw [mul_one]
  | solve
    | simp [Int.ModEq]
  | solve
    | simp [Nat.modEq_iff_dvd]
  | solve
    | simp only [Nat.ModEq, pow_two, mul_one]
      norm_num
  | solve
    | simp only [Nat.modEq_iff_dvd, pow_two, pow_mul, Nat.cast_pow]
      norm_num
  | solve
    | simp [Nat.ModEq, Int.ModEq]
example : ((5^(2*1) ≡ 25 [ZMOD 100])) := @solution
#print axioms solution
