-- Prove2me | solution 1 for WorkbookSource.problem_3247
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:06.424459+00:00
-- url     : https://prove2.me/submissions/2d7163fa-e5d4-4f58-9f64-f08aac78ba97

/- InternLM Lean-Workbook, lean_workbook_3247, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (y z : ℝ) :
  (y * z - 2 * y - 2 * z)^2 ≥ 2 * y * z * (2 - y - z)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf
      simp [sq]
      nlinarith [sq_nonneg (y * z - 2 * y - 2 * z)]
  | solve
    | simp [sq]
      ring_nf
      nlinarith [sq_nonneg (y * z - 2 * y - 2 * z)]
example : (∀ (y z : ℝ), (y * z - 2 * y - 2 * z)^2 ≥ 2 * y * z * (2 - y - z)) := @solution
#print axioms solution
