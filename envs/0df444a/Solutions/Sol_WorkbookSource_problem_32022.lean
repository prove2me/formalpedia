-- Prove2me | solution 1 for WorkbookSource.problem_32022
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:25.212013+00:00
-- url     : https://prove2.me/submissions/fc5bf575-38dd-4990-b059-f15cca4b430f

/- Source: InternLM Lean-Workbook, record lean_workbook_32022.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) = 7 / 3 → a ^ 3 + b ^ 3 + c ^ 3 >= 5 * a * b * c) := by
  first
  | solve
    | field_simp [ha.ne', hb.ne', hc.ne']
      ring_nf
      norm_num
      intro h
      nlinarith [h]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) = 7 / 3 → a ^ 3 + b ^ 3 + c ^ 3 >= 5 * a * b * c)) := @solution
#print axioms solution
