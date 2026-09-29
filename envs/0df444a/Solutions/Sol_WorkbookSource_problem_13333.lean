-- Prove2me | solution 1 for WorkbookSource.problem_13333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:25.965013+00:00
-- url     : https://prove2.me/submissions/85e13c1a-83a7-4989-b4c5-295b9f823ed4

/- InternLM Lean-Workbook, lean_workbook_13333, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (y : ℝ)
  (h₀ : 0 ≤ y)
  (h₁ : y ≤ 1) :
  y^2 - (2 * y^3) / 3 ≤ 1 / 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have h₂ := sq_nonneg (1 - y)
      nlinarith
  | solve
    | rw [← sub_nonneg]
      have := sq_nonneg (1 - y)
      nlinarith
example : (∀ (y : ℝ)
  (h₀ : 0 ≤ y)
  (h₁ : y ≤ 1), y^2 - (2 * y^3) / 3 ≤ 1 / 3) := @solution
#print axioms solution
