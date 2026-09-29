-- Prove2me | solution 1 for WorkbookSource.problem_18562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:45.576906+00:00
-- url     : https://prove2.me/submissions/c5996b82-6365-40c5-9768-58e4d85da098

/- InternLM Lean-Workbook, lean_workbook_18562, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  499 ∣ (10^498 - 1)/9  := by
  norm_num
example : (499 ∣ (10^498 - 1)/9) := @solution
#print axioms solution
