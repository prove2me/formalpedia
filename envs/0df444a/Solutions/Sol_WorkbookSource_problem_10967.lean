-- Prove2me | solution 1 for WorkbookSource.problem_10967
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:23.431527+00:00
-- url     : https://prove2.me/submissions/79e7697f-1ed8-4b5a-9691-05853ad64db9

/- InternLM Lean-Workbook, lean_workbook_10967, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0): 3 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a + b + c) = 48 → a ^ 2 + b ^ 2 + c ^ 2 ≥ 12  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro h
      linarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2)]
  | solve
    | intro h
      have : 0 ≤ (a - 2)^2 + (b - 2)^2 + (c - 2)^2 := by positivity
      nlinarith [h]
  | solve
    | intro h
      have := sq_nonneg (a - 2)
      have := sq_nonneg (b - 2)
      have := sq_nonneg (c - 2)
      linarith
  | solve
    | intro h
      have h1 := sq_nonneg (a - 2)
      have h2 := sq_nonneg (b - 2)
      have h3 := sq_nonneg (c - 2)
      linarith
  | solve
    | intro h
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2)]
  | solve
    | intro h
      have := sq_nonneg (a - 2)
      have := sq_nonneg (b - 2)
      have := sq_nonneg (c - 2)
      nlinarith
  | solve
    | intro h
      have h1 := sq_nonneg (a - 2)
      have h2 := sq_nonneg (b - 2)
      have h3 := sq_nonneg (c - 2)
      nlinarith
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), 3 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a + b + c) = 48 → a ^ 2 + b ^ 2 + c ^ 2 ≥ 12) := @solution
#print axioms solution
