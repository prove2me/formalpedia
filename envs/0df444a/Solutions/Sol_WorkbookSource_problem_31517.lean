-- Prove2me | solution 1 for WorkbookSource.problem_31517
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:24.361302+00:00
-- url     : https://prove2.me/submissions/c63c7a4d-1e83-43dc-9de3-205b4759802b

/- Source: InternLM Lean-Workbook, record lean_workbook_31517.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a < 2 ∧ b < 2) : a^2 + a * b + b^2 < 3 * (a + b) := by
  first
  | solve
    | repeat nlinarith [h1, h2]
  | solve
    | field_simp [sq]
      nlinarith
  | solve
    | field_simp [pow_two]
      nlinarith
  | solve
    | nlinarith [pow_two_nonneg a, pow_two_nonneg b]
  | solve
    | have h3 : 0 < a + b := add_pos h1.1 h1.2
      field_simp [pow_two]
      nlinarith [h1, h2, h3]
  | solve
    | have h3 : 0 < a + b := add_pos h1.1 h1.2
      field_simp [h1.1, h1.2, h3]
      nlinarith [h1, h2]

example : (∀ (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a < 2 ∧ b < 2), a^2 + a * b + b^2 < 3 * (a + b)) := @solution
#print axioms solution
