-- Prove2me | solution 1 for WorkbookSource.problem_18636
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:46.316987+00:00
-- url     : https://prove2.me/submissions/9dddf8fa-99e4-4691-b637-a6dc6fcf6d3d

/- InternLM Lean-Workbook, lean_workbook_18636, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2 ^ 2009 ≡ 6 [ZMOD 13]  := by
  norm_num [Int.ModEq]
example : (2 ^ 2009 ≡ 6 [ZMOD 13]) := @solution
#print axioms solution
