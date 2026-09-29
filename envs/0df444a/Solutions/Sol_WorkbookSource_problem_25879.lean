-- Prove2me | solution 1 for WorkbookSource.problem_25879
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:39.380755+00:00
-- url     : https://prove2.me/submissions/91da8ba1-2142-4453-92b8-f2eaec066a14

/- InternLM Lean-Workbook, lean_workbook_25879, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  Nat.gcd (2^20 - 1) (2^110 - 1) = 1023  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num at *
  | solve
    | norm_num [pow_one]
  | solve
    | simp [Nat.gcd_comm]
  | solve
    | simp [Nat.gcd_rec 1]
example : (Nat.gcd (2^20 - 1) (2^110 - 1) = 1023) := @solution
#print axioms solution
