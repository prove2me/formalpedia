-- Prove2me | solution 1 for WorkbookSource.plus_54193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:16.711624+00:00
-- url     : https://prove2.me/submissions/2166d4d4-d163-481a-8d3e-92d247bbfdff

/- InternLM Lean-Workbook, lean_workbook_plus_54193, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ZMod 59) : ¬(x^2 + x + 1 = 0)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | revert x
      decide
example : (∀ (x : ZMod 59), ¬(x^2 + x + 1 = 0)) := @solution
#print axioms solution
