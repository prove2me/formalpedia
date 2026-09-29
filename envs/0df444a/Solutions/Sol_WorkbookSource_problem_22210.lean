-- Prove2me | solution 1 for WorkbookSource.problem_22210
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:52.964961+00:00
-- url     : https://prove2.me/submissions/6617f061-533d-411c-b3a1-919b6bd3736d

/- Source: InternLM Lean-Workbook, record lean_workbook_22210.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) : 64 * a ^ 6 - 192 * a ^ 5 + 176 * a ^ 4 - 32 * a ^ 3 + 116 * a ^ 2 - 132 * a + 223 > 0 := by
  obtain ⟨ha1, ha2⟩ := ha
  nlinarith [pow_nonneg ha1 6, pow_le_one₀ (n := 6) ha1 ha2]

example : (∀ (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1), 64 * a ^ 6 - 192 * a ^ 5 + 176 * a ^ 4 - 32 * a ^ 3 + 116 * a ^ 2 - 132 * a + 223 > 0) := @solution
#print axioms solution
