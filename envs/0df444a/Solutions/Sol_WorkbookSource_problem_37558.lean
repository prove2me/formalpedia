-- Prove2me | solution 1 for WorkbookSource.problem_37558
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:41.287743+00:00
-- url     : https://prove2.me/submissions/7ff45356-b8e1-4a6b-858b-d7aaf0821e69

/- InternLM Lean-Workbook, lean_workbook_37558, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : √(2014*2015*2016*2017 + 1) = 4062239  := by
  first
  | solve
    | norm_num [Real.sqrt_eq_iff_sq_eq]
  | solve
    | norm_num [sqrt_eq_iff_mul_self_eq_of_pos, mul_pos]
  | solve
    | rw [sqrt_eq_iff_mul_self_eq]
      all_goals norm_num
  | solve
    | rw [Real.sqrt_eq_iff_sq_eq]
      all_goals { norm_num }
  | solve
    | ring_nf
      norm_num [Real.sqrt_eq_iff_sq_eq]
  | solve
    | rw [sqrt_eq_iff_mul_self_eq] <;> norm_num
  | solve
    | rw [sqrt_eq_iff_sq_eq]
      all_goals norm_num
  | solve
    | rw [sqrt_eq_iff_sq_eq]
      norm_num
      linarith
      linarith
  | solve
    | rw [sqrt_eq_iff_mul_self_eq]
      all_goals norm_num [Int.mul_ediv_cancel_left]
  | solve
    | rw [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | solve
    | rw [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
  | solve
    | rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  | solve
    | rw [sqrt_eq_iff_sq_eq] <;> norm_num
  | solve
    | rw [sqrt_eq_iff_mul_self_eq]
      all_goals { norm_num }
example : (√(2014*2015*2016*2017 + 1) = 4062239) := @solution
#print axioms solution
