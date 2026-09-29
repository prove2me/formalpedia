-- Prove2me | solution 1 for WorkbookSource.problem_41226
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:09.75005+00:00
-- url     : https://prove2.me/submissions/f40d1404-8991-47d8-acf4-a2ffd3719269

/- InternLM Lean-Workbook, lean_workbook_41226, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Complex
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x y : ℂ, (2 * x ^ 2 - 3 * x * y + y ^ 2 = 0) ↔ (x - y) * (2 * x - y) = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x y
      ring_nf
  | solve
    | intro x y; ring_nf
  | solve
    | rintro a b
      ring_nf
  | solve
    | rintro x y
      ring_nf
  | solve
    | intros x y
      ring_nf
example : (∀ x y : ℂ, (2 * x ^ 2 - 3 * x * y + y ^ 2 = 0) ↔ (x - y) * (2 * x - y) = 0) := @solution
#print axioms solution
