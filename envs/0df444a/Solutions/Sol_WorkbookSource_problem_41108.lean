-- Prove2me | solution 1 for WorkbookSource.problem_41108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:52.539896+00:00
-- url     : https://prove2.me/submissions/4c3fa10e-b666-4598-9d61-cd5f0f8d0c63

/- InternLM Lean-Workbook, lean_workbook_41108, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution :
  ((56 * 7 + 35 * 8) : ℚ) / (choose 15 4 : ℚ) = 32 / 65  := by
  first
  | solve
    | norm_num [Nat.choose]
  | solve
    | rw [div_eq_mul_inv]
      norm_num [choose]
  | solve
    | conv_lhs => rw [← Nat.cast_eq_ofNat]
  | solve
    | norm_num [choose, Nat.factorial]
  | solve
    | ring_nf
      norm_cast at *
  | solve
    | norm_num [pow_succ, choose]
  | solve
    | norm_cast at *
  | solve
    | simp only [Nat.choose]
      norm_num [div_eq_mul_inv, inv_eq_one_div]
  | solve
    | norm_num [Nat.choose]
  | solve
    | simp [Nat.choose]
      norm_num [div_eq_mul_inv]
example : (((56 * 7 + 35 * 8) : ℚ) / (choose 15 4 : ℚ) = 32 / 65) := @solution
#print axioms solution
