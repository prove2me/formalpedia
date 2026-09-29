-- Prove2me | solution 1 for WorkbookSource.problem_53396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:41.131764+00:00
-- url     : https://prove2.me/submissions/4b20fdfd-e1df-4690-aefd-ff36e1acda08

/- Source: InternLM Lean-Workbook, record lean_workbook_53396.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : min (a + b) c ≤ min a c + min b c := by
  first
  | solve
    | cases le_total a c <;> cases le_total b c <;> simp [*]
  | solve
    | simp only [min_def, ha, hb, hc, if_true, if_false, le_refl, add_comm, add_left_comm, add_assoc]
      split_ifs <;> linarith

example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), min (a + b) c ≤ min a c + min b c) := @solution
#print axioms solution
