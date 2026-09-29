-- Prove2me | solution 1 for WorkbookSource.problem_42346
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:32.908968+00:00
-- url     : https://prove2.me/submissions/f163cb56-3174-41a2-ab9e-85aeb4afe47e

/- Source: InternLM Lean-Workbook, record lean_workbook_42346.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) : x^4 + 25*y^4 + 30*x^2*y^2 ≥ 40*x*y^3 + 8*x^3*y := by
  first
  | solve
    | nlinarith [sq_nonneg (x^2 + 5*y^2 - 4*x*y)]
  | solve
    | have := sq_nonneg (x^2 + 5*y^2 - 4*x*y)
      nlinarith
  | solve
    | nlinarith [sq_nonneg (x - 2*y), sq_nonneg (x + 3*y)]
  | solve
    | nlinarith [sq_nonneg (x - 2*y), sq_nonneg (x - 5*y)]
  | solve
    | field_simp
      nlinarith [sq_nonneg (x^2 + 5*y^2 - 4*x*y)]
  | solve
    | have h0: 0 ≤ (x - 2*y)^2 := sq_nonneg (x - 2*y)
      nlinarith

example : (∀ (x y : ℝ), x^4 + 25*y^4 + 30*x^2*y^2 ≥ 40*x*y^3 + 8*x^3*y) := @solution
#print axioms solution
