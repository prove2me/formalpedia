-- Prove2me | solution 1 for WorkbookSource.problem_26614
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:41.100528+00:00
-- url     : https://prove2.me/submissions/658a854d-b71e-4df9-82bf-2f0e0477fe98

/- InternLM Lean-Workbook, lean_workbook_26614, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | apply_rules [add_nonneg, div_nonneg] <;> linarith [h1]
  | solve
    | apply_rules [add_nonneg, div_nonneg] <;> linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  | solve
    | rw [← add_zero (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))]
      apply add_nonneg
      apply_rules [add_nonneg, div_nonneg, add_nonneg]
      repeat' linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  | solve
    | apply_rules [add_nonneg, div_nonneg] <;> nlinarith [h1]
  | solve
    | apply_rules [add_nonneg, div_nonneg] <;> nlinarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  | solve
    | rw [← add_zero (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))]
      apply add_nonneg
      apply_rules [add_nonneg, div_nonneg, add_nonneg]
      repeat' nlinarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
example : (∀ (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1), 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0) := @solution
#print axioms solution
