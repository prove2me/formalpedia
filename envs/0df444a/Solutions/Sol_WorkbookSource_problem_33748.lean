-- Prove2me | solution 1 for WorkbookSource.problem_33748
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:27.493994+00:00
-- url     : https://prove2.me/submissions/6748abe2-df40-435a-8e38-a6b3bdbdd323

/- Source: InternLM Lean-Workbook, record lean_workbook_33748.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution : ∀ x : ℝ, ¬(8*x^8 + 3*x^6 + 5*x^4 + 3*x^2 + 10 = 0) := by
  first
  | solve
    | refine' fun x => ne_of_gt _
      positivity
  | solve
    | intro x
      nlinarith [pow_two_nonneg (x^2)]
  | solve
    | intro x
      nlinarith [pow_two_nonneg (2*x^2)]
  | solve
    | intro x
      nlinarith [sq_nonneg x, sq_nonneg (x^2)]
  | solve
    | intro x
      nlinarith [sq_nonneg (x^2+1), sq_nonneg (x^2-1)]
  | solve
    | intros x
      nlinarith [pow_two_nonneg x, pow_two_nonneg (x^3)]

example : (∀ x : ℝ, ¬(8*x^8 + 3*x^6 + 5*x^4 + 3*x^2 + 10 = 0)) := @solution
#print axioms solution
