-- Prove2me | solution 1 for WorkbookSource.problem_32495
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:24.961469+00:00
-- url     : https://prove2.me/submissions/214c6744-7ddb-49d0-be4b-343a4f7e5625

/- InternLM Lean-Workbook, lean_workbook_32495, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 123 ≡ (1 + 2 + 3) [ZMOD 9]  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | conv_lhs => norm_num
  | solve
    | rw [Int.ModEq]
      norm_num
  | solve
    | simp only [Int.ModEq]
      ring
  | solve
    | simp only [Int.ModEq]
      decide
example : (123 ≡ (1 + 2 + 3) [ZMOD 9]) := @solution
#print axioms solution
