-- Prove2me | solution 1 for WorkbookSource.problem_12643
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:44.228707+00:00
-- url     : https://prove2.me/submissions/8a60d2e4-7ad0-4e70-9b70-9f35bc81b72c

/- InternLM Lean-Workbook, lean_workbook_12643, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 23 ^ 2007 ≡ 7 [MOD 10]  := by
  norm_num [Nat.ModEq, Nat.pow_mod]
example : (23 ^ 2007 ≡ 7 [MOD 10]) := @solution
#print axioms solution
