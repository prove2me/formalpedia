-- Prove2me | solution 1 for WorkbookSource.plus_82261
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:37.705351+00:00
-- url     : https://prove2.me/submissions/e8bbd2b6-1c31-4eed-a3d5-df98b77af4b9

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_82261.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0)(hab : a + b^2 + c^2 = 4) : a^2 + b^2 + c^2 ≥ 15 / 4 := by
  first
  | solve
    | have h1 := sq_nonneg (a - 1/2)
      have h2 := sq_nonneg (b - 1/2)
      have h3 := sq_nonneg (c - 1/2)
      linarith
  | solve
    | have h1 := sq_nonneg (a - 1 / 2)
      have h2 := sq_nonneg (b - 1 / 2)
      have h3 := sq_nonneg (c - 1 / 2)
      linarith [ha.1, ha.2.1, ha.2.2, hab, h1, h2, h3]

example : (∀ (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0)(hab : a + b^2 + c^2 = 4), a^2 + b^2 + c^2 ≥ 15 / 4) := @solution
#print axioms solution
