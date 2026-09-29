-- Prove2me | solution 1 for WorkbookSource.problem_52474
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:05.908358+00:00
-- url     : https://prove2.me/submissions/e930e727-bfc2-4056-9257-d37155203e78

/- InternLM Lean-Workbook, lean_workbook_52474, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℕ → ℝ) (hx: x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ x 5 ∧ x 5 ≤ x 6 ∧ x 6 ≤ x 7): x 5 + x 6 + x 7 ≥ 3/7 * (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith only [hx]
  | solve
    | field_simp at *
      linarith
  | solve
    | simp only [ge_iff_le]
      linarith
  | solve
    | simp only [ge_iff_le]
      nlinarith
  | solve
    | nlinarith only [hx]
  | solve
    | field_simp at *
      nlinarith
  | solve
    | simp only [ge_iff_le]
      nlinarith
example : (∀ (x : ℕ → ℝ) (hx: x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ x 5 ∧ x 5 ≤ x 6 ∧ x 6 ≤ x 7), x 5 + x 6 + x 7 ≥ 3/7 * (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7)) := @solution
#print axioms solution
