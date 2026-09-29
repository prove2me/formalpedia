-- Prove2me | solution 1 for WorkbookSource.problem_21025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:00.982124+00:00
-- url     : https://prove2.me/submissions/31703c28-1db6-42b3-a089-2be0490246f4

/- InternLM Lean-Workbook, lean_workbook_21025, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (8 * 4 + 2) - (8 + 4 * 2) = 18  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp only [mul_comm]
  | solve
    | simp only [Nat.mul_comm]
  | solve
    | field_simp [Nat.mul_comm]
  | solve
    | norm_num [mul_add, add_mul]
example : ((8 * 4 + 2) - (8 + 4 * 2) = 18) := @solution
#print axioms solution
