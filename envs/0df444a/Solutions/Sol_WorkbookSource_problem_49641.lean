-- Prove2me | solution 1 for WorkbookSource.problem_49641
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:55.072732+00:00
-- url     : https://prove2.me/submissions/14085f7a-4e47-46d5-834e-11d0b8257401

/- InternLM Lean-Workbook, lean_workbook_49641, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (10 ^ 2011 - 1) / 9 ≡ 1 [ZMOD 4022]  := by
  norm_num

example : ((10 ^ 2011 - 1) / 9 ≡ 1 [ZMOD 4022]) := @solution
#print axioms solution
