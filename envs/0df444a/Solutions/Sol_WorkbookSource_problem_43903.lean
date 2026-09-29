-- Prove2me | solution 1 for WorkbookSource.problem_43903
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:33.691359+00:00
-- url     : https://prove2.me/submissions/0a4e1efd-9cdd-4a97-b9e8-9705a2da715f

/- Source: InternLM Lean-Workbook, record lean_workbook_43903.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) : a + (b + c) / 2 = (a + b) / 2 + (a + c) / 2 := by
  first
  | solve
    | linarith [b]
  | solve
    | field_simp; ring
  | solve
    | ring_nf at a b c ⊢
  | solve
    | linarith [a, b, c]
  | solve
    | linarith [a + b + c]
  | solve
    | linarith only [b, c]

example : (∀ (a b c : ℝ), a + (b + c) / 2 = (a + b) / 2 + (a + c) / 2) := @solution
#print axioms solution
