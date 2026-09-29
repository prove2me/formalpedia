-- Prove2me | solution 1 for WorkbookSource.problem_25493
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:38.538748+00:00
-- url     : https://prove2.me/submissions/a123ed42-e9b5-401a-aac9-20ca822d1e9e

/- InternLM Lean-Workbook, lean_workbook_25493, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : 3 - x ≥ 0 ↔ x ≤ 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [ge_iff_le, sub_nonneg]
  | solve
    | simp only [ge_iff_le, sub_nonneg]
  | solve
    | simp only [sub_nonneg, ge_iff_le]
  | solve
    | rw [sub_eq_add_neg]
      simp [add_comm]
example : (∀ (x : ℝ), 3 - x ≥ 0 ↔ x ≤ 3) := @solution
#print axioms solution
