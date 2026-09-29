-- Prove2me | solution 1 for WorkbookSource.problem_34802
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:47.618487+00:00
-- url     : https://prove2.me/submissions/bf29d772-576c-4448-b468-0069c5acd2d9

/- InternLM Lean-Workbook, lean_workbook_34802, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) : (a^2 + a * b + b^2) * (a^2 + a * c + c^2) - (a^2 + a * (b + c) / 2 + b * c)^2 = 3 / 4 * a^2 * (b - c)^2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sq]
      ring
  | solve
    | rw [mul_add]
      ring
  | solve
    | simp [sq]
      ring_nf
  | solve
    | simp [add_sq]
      ring
example : (∀ (a b c : ℝ), (a^2 + a * b + b^2) * (a^2 + a * c + c^2) - (a^2 + a * (b + c) / 2 + b * c)^2 = 3 / 4 * a^2 * (b - c)^2) := @solution
#print axioms solution
