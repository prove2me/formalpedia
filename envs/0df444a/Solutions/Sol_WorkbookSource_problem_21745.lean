-- Prove2me | solution 1 for WorkbookSource.problem_21745
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:02.330979+00:00
-- url     : https://prove2.me/submissions/f70fafdd-e739-4636-8b54-851f0a94c9ab

/- InternLM Lean-Workbook, lean_workbook_21745, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x a b : ℝ) (hx : x ≥ 0 ∧ a^3 - 4 = 4 - b^3) : a^3 + b^3 - 8 = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [hx]
  | solve
    | linarith only [hx]
  | solve
    | nlinarith only [hx]
  | solve
    | linarith [hx.1, hx.2]
  | solve
    | nlinarith only [hx]
  | solve
    | nlinarith [hx.1, hx.2]
example : (∀ (x a b : ℝ) (hx : x ≥ 0 ∧ a^3 - 4 = 4 - b^3), a^3 + b^3 - 8 = 0) := @solution
#print axioms solution
