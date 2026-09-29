-- Prove2me | solution 1 for WorkbookSource.problem_20060
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:49.948332+00:00
-- url     : https://prove2.me/submissions/62a236db-adb6-48bf-b641-e388f1efc7e3

/- Source: InternLM Lean-Workbook, record lean_workbook_20060.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b: ℝ) (hab : a^2 + b^2 = 1): (a + 1) * (b + 2) < 5 := by
  first
  | solve
    | nlinarith [sq_nonneg (a - b), hab]
  | solve
    | have : a^2 + b^2 = 1 := hab
      nlinarith [sq_nonneg (a - b)]
  | solve
    | have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
      nlinarith [hab]
  | solve
    | have h1 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
      nlinarith [h1]

example : (∀ (a b: ℝ) (hab : a^2 + b^2 = 1), (a + 1) * (b + 2) < 5) := @solution
#print axioms solution
