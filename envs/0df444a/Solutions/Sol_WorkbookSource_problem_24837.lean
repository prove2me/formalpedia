-- Prove2me | solution 1 for WorkbookSource.problem_24837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:50.130532+00:00
-- url     : https://prove2.me/submissions/c5be0e24-ef95-448b-9e7f-25b1b6651e66

/- InternLM Lean-Workbook, lean_workbook_24837, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2000 * (2000 ^ 2000) = 2000 ^ 2001  := by
  exact (pow_succ' (2000 : ℕ) 2000).symm

example : (2000 * (2000 ^ 2000) = 2000 ^ 2001) := @solution
#print axioms solution
