-- Prove2me | solution 1 for WorkbookSource.problem_27495
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:12.409375+00:00
-- url     : https://prove2.me/submissions/d2cd56c7-d062-49df-8b23-e1f2029991f1

/- InternLM Lean-Workbook, lean_workbook_27495, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (h : ∀ x y, f x - x = f y - y) : ∀ x, f x = x + f 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x
      symm
      linarith [h x 0]
  | solve
    | intro x
      have := h x 0
      linarith
  | solve
    | rintro x
      linarith [h x 0, h 0 0]
  | solve
    | intro x
      specialize h x 0
      linarith
  | solve
    | intro x
      symm
      nlinarith [h x 0]
  | solve
    | intro x
      have := h x 0
      nlinarith
  | solve
    | rintro x
      nlinarith [h x 0, h 0 0]
  | solve
    | intro x
      specialize h x 0
      nlinarith
example : (∀ (f : ℝ → ℝ) (h : ∀ x y, f x - x = f y - y), ∀ x, f x = x + f 0) := @solution
#print axioms solution
