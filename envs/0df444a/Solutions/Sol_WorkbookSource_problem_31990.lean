-- Prove2me | solution 1 for WorkbookSource.problem_31990
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:22.789535+00:00
-- url     : https://prove2.me/submissions/3ff7f520-adeb-4fee-9ce7-b050b7aeffcc

/- InternLM Lean-Workbook, lean_workbook_31990, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (100:ℝ)^101 > 101^100  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [pow_succ]
  | solve
    | nlinarith [101, 100]
  | solve
    | norm_num [Nat.factorial]
  | solve
    | norm_num [Nat.lt_succ_self]
example : ((100:ℝ)^101 > 101^100) := @solution
#print axioms solution
