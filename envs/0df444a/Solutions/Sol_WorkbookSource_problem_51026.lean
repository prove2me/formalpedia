-- Prove2me | solution 1 for WorkbookSource.problem_51026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:43.749302+00:00
-- url     : https://prove2.me/submissions/aa2e00d0-b201-4dad-9a85-7aead53c033d

/- InternLM Lean-Workbook, lean_workbook_51026, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 3 ∣ 2^2010 + 3^2010 + 5^2010 + 67^2010  := by
  norm_num

example : (3 ∣ 2^2010 + 3^2010 + 5^2010 + 67^2010) := @solution
#print axioms solution
