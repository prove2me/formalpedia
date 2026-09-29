-- Prove2me | solution 1 for WorkbookSource.problem_23797
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:07.327243+00:00
-- url     : https://prove2.me/submissions/f2069d74-3518-4ec4-bcb8-2a3d5d799110

/- InternLM Lean-Workbook, lean_workbook_23797, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x y z : ℝ, (4 * x ^ 3 - 4 * x ^ 2 + x + 4 * y ^ 3 - 4 * y ^ 2 + y + 4 * z ^ 3 - 4 * z ^ 2 + z ≥ 0 ↔ x * (2 * x - 1) ^ 2 + y * (2 * y - 1) ^ 2 + z * (2 * z - 1) ^ 2 ≥ 0)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x y z
      ring_nf
  | solve
    | intros
      simp [add_comm]
      ring_nf
  | solve
    | simp [sub_nonneg]
      intros
      ring_nf
  | solve
    | intro x y z
      simp [add_comm]
      norm_num
      ring_nf
example : (∀ x y z : ℝ, (4 * x ^ 3 - 4 * x ^ 2 + x + 4 * y ^ 3 - 4 * y ^ 2 + y + 4 * z ^ 3 - 4 * z ^ 2 + z ≥ 0 ↔ x * (2 * x - 1) ^ 2 + y * (2 * y - 1) ^ 2 + z * (2 * z - 1) ^ 2 ≥ 0)) := @solution
#print axioms solution
