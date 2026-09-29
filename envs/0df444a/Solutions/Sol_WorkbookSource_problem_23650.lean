-- Prove2me | solution 1 for WorkbookSource.problem_23650
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:06.480305+00:00
-- url     : https://prove2.me/submissions/54c659be-1fea-4764-8d50-d733e05ad133

/- InternLM Lean-Workbook, lean_workbook_23650, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : x ≥ 1) : x^2 + 1/9 * (2 - x) * (11 + 4 * x) ≥ 2/3 * x + 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [hx]
  | solve
    | nlinarith [hx, hx]
  | solve
    | field_simp [mul_comm]
      nlinarith
  | solve
    | ring_nf
      norm_num
      nlinarith [hx]
example : (∀ (x : ℝ) (hx : x ≥ 1), x^2 + 1/9 * (2 - x) * (11 + 4 * x) ≥ 2/3 * x + 2) := @solution
#print axioms solution
