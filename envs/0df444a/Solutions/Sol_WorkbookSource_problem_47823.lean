-- Prove2me | solution 1 for WorkbookSource.problem_47823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:57.573057+00:00
-- url     : https://prove2.me/submissions/a20a95f0-d8ad-4f18-9ea5-6b63a5dd2dd4

/- InternLM Lean-Workbook, lean_workbook_47823, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℚ) (h : a = 1 / 4 * (2 / 9 * (1 / 2))) : a = 1 / 36  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [h]
  | solve
    | norm_num [h]
  | solve
    | linear_combination h
  | solve
    | rw [h]
      ring_nf at h ⊢
  | solve
    | nlinarith [h]
example : (∀ (a : ℚ) (h : a = 1 / 4 * (2 / 9 * (1 / 2))), a = 1 / 36) := @solution
#print axioms solution
