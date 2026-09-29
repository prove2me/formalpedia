-- Prove2me | solution 1 for WorkbookSource.plus_44787
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:32.160609+00:00
-- url     : https://prove2.me/submissions/ada1ad90-0391-4b17-8427-209c2ac0c3be

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_44787.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b : ℝ) (h : a ^ 2 + b ^ 2 = 8) : -12 ≤ 2 * (a + b) - a * b ∧ 2 * (a + b) - a * b ≤ 6 := by
  first
  | solve
    | apply And.intro
      nlinarith [sq_nonneg (a - b)]
      nlinarith [sq_nonneg (a + b - 2)]

example : (∀ (a b : ℝ) (h : a ^ 2 + b ^ 2 = 8), -12 ≤ 2 * (a + b) - a * b ∧ 2 * (a + b) - a * b ≤ 6) := @solution
#print axioms solution
