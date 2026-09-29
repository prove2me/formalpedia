-- Prove2me | solution 1 for WorkbookSource.problem_28817
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:17.579727+00:00
-- url     : https://prove2.me/submissions/e7de6dcb-effe-46bb-9b82-2afe58b2c844

/- InternLM Lean-Workbook, lean_workbook_28817, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℚ) (h : a = 20 * 22 * 24 / (10 * 11 * 12)) : a = 8  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [h]
      ring
  | solve
    | simp [h]
      ring
  | solve
    | rw [h]
      ring_nf
  | solve
    | rw [h]
      norm_num
example : (∀ (a : ℚ) (h : a = 20 * 22 * 24 / (10 * 11 * 12)), a = 8) := @solution
#print axioms solution
