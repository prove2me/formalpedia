-- Prove2me | solution 1 for WorkbookSource.problem_15655
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:36.001073+00:00
-- url     : https://prove2.me/submissions/ff2fe9f4-7947-4f78-aab1-116fabe378c5

/- InternLM Lean-Workbook, lean_workbook_15655, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) : (a / b - 1 / 2) * (a / b - 2) ≤ 0 → a^2 / b^2 + 1 ≤ 5 * a / (2 * b)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro h
      ring_nf at *
      linarith
  | solve
    | intro h
      ring_nf at h ⊢
      nlinarith
  | solve
    | contrapose!
      intro h
      ring_nf at *
      nlinarith
  | solve
    | intro h
      field_simp at h ⊢
      ring_nf at h ⊢
      nlinarith [h]
  | solve
    | intro h
      ring_nf at *
      nlinarith
example : (∀ (a b : ℝ), (a / b - 1 / 2) * (a / b - 2) ≤ 0 → a^2 / b^2 + 1 ≤ 5 * a / (2 * b)) := @solution
#print axioms solution
