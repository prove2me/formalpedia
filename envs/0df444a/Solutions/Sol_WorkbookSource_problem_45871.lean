-- Prove2me | solution 1 for WorkbookSource.problem_45871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:13.565076+00:00
-- url     : https://prove2.me/submissions/b725beb5-cf17-42e3-b0c5-a17747a216d3

/- InternLM Lean-Workbook, lean_workbook_45871, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : (101!)^100 > (100!)^101  := by
  first
  | solve
    | decide +kernel
  | solve
    | norm_num [Nat.factorial_succ, pow_succ, mul_pow]
  | solve
    | norm_num [Nat.factorial_succ, pow_succ]
  | solve
    | norm_num [Nat.factorial_succ, Nat.pow_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
  | solve
    | norm_num [Nat.factorial_succ, Nat.pow_succ, Nat.pow_succ]
  | solve
    | rw [pow_succ]
      norm_cast
  | solve
    | norm_num [Nat.factorial_succ, Nat.factorial_zero]
  | solve
    | simp only [Nat.factorial]
      norm_num [Nat.factorial]
  | solve
    | norm_num [Nat.factorial_succ, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  | solve
    | norm_num [Nat.pow_succ, Nat.factorial_succ, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
  | solve
    | norm_num [Nat.factorial_succ, Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
example : ((101!)^100 > (100!)^101) := @solution
#print axioms solution
