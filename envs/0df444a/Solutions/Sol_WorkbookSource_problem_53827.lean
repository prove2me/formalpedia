-- Prove2me | solution 1 for WorkbookSource.problem_53827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:43.676281+00:00
-- url     : https://prove2.me/submissions/bdfee398-e2a9-4f5e-b369-8a0c4976e667

/- Source: InternLM Lean-Workbook, record lean_workbook_53827.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) : a ^ 4 + b ^ 2 * c ^ 2 ≥ 2 * a ^ 2 * b * c := by
  first
  | solve
    | nlinarith [sq_nonneg (a^2 - b * c)]
  | solve
    | nlinarith [sq_nonneg (b * c - a ^ 2)]
  | solve
    | nlinarith [sq_nonneg (a ^ 2 - b * c)]
  | solve
    | have h1 := sq_nonneg (a^2 - b * c)
      linarith
  | solve
    | have h₁ := sq_nonneg (a ^ 2 - b * c)
      linarith
  | solve
    | have h1 := sq_nonneg (a ^ 2 - b * c)
      nlinarith

example : (∀ (a b c : ℝ), a ^ 4 + b ^ 2 * c ^ 2 ≥ 2 * a ^ 2 * b * c) := @solution
#print axioms solution
