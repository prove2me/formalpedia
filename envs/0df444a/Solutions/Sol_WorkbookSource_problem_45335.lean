-- Prove2me | solution 1 for WorkbookSource.problem_45335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:34.393566+00:00
-- url     : https://prove2.me/submissions/e1d15ff2-35fe-4cc5-9700-b46af8760123

/- Source: InternLM Lean-Workbook, record lean_workbook_45335.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (c : ℝ) (h : c > 3/4) : ¬ (∃ x, 4*x^4 - 2*x + c = 0) := by
  first
  | solve
    | push_neg
      intro x
      nlinarith [sq_nonneg (2 * x - 1), sq_nonneg (2 * x + 1)]
  | solve
    | contrapose! h
      obtain ⟨x, hx⟩ := h
      have := sq_nonneg (x - 1/2)
      have := sq_nonneg (x + 1/2)
      nlinarith
  | solve
    | contrapose! h
      obtain ⟨x, hx⟩ := h
      have h1 := sq_nonneg (2*x - 1)
      have h2 := sq_nonneg (2*x + 1)
      nlinarith

example : (∀ (c : ℝ) (h : c > 3/4), ¬ (∃ x, 4*x^4 - 2*x + c = 0)) := @solution
#print axioms solution
