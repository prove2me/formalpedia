-- Prove2me | solution 1 for WorkbookSource.problem_53405
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:08.188526+00:00
-- url     : https://prove2.me/submissions/dae0400c-7528-4ebd-b808-52daf280d338

/- InternLM Lean-Workbook, lean_workbook_53405, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 19 ≡ -6 [ZMOD 5]  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [Int.ModEq]
  | solve
    | conv_rhs => norm_num
  | solve
    | norm_num [Int.ModEq]
  | solve
    | rw [Int.ModEq]
      decide
example : (19 ≡ -6 [ZMOD 5]) := @solution
#print axioms solution
