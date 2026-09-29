-- Prove2me | solution 1 for WorkbookSource.plus_41247
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:15.086334+00:00
-- url     : https://prove2.me/submissions/c071c34b-fe76-4785-b1b3-38e6576475d9

/- InternLM Lean-Workbook, lean_workbook_plus_41247, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) (b : ℝ) (c : ℝ) (ha : a > 0) (h : b^2 - 4*a*c < 0) : ¬ (∃ x, a*x^2 + b*x + c = 0)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro ⟨x, hx⟩
      nlinarith [sq_nonneg (b + 2 * a * x)]
  | solve
    | contrapose! h
      obtain ⟨x, hx⟩ := h
      nlinarith [sq_nonneg (b + 2 * a * x)]
  | solve
    | contrapose! h
      obtain ⟨x, hx⟩ := h
      have := sq_nonneg (b + 2 * a * x)
      nlinarith
  | solve
    | simp only [not_exists, not_and]
      intro x hx
      nlinarith [sq_nonneg (b + 2 * a * x)]
example : (∀ (a : ℝ) (b : ℝ) (c : ℝ) (ha : a > 0) (h : b^2 - 4*a*c < 0), ¬ (∃ x, a*x^2 + b*x + c = 0)) := @solution
#print axioms solution
