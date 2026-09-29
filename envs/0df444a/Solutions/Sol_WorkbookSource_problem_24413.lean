-- Prove2me | solution 1 for WorkbookSource.problem_24413
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:34.051034+00:00
-- url     : https://prove2.me/submissions/5f17383d-fc1b-444a-99a3-19908b1892fa

/- InternLM Lean-Workbook, lean_workbook_24413, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x > 1/4, Real.sqrt x < 2 * x  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x hx
      rw [sqrt_lt (by positivity)]
      nlinarith
      positivity
  | solve
    | intro x hx
      rw [Real.sqrt_lt (by positivity)]
      nlinarith
      positivity
  | solve
    | intro x hx
      rw [Real.sqrt_lt (by positivity)]
      ring_nf
      nlinarith
      positivity
  | solve
    | intro x hx
      rw [Real.sqrt_lt (by positivity)]
      push_cast
      nlinarith only [hx]
      positivity
example : (∀ x > 1/4, Real.sqrt x < 2 * x) := @solution
#print axioms solution
