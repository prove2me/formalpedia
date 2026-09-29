-- Prove2me | solution 1 for WorkbookSource.problem_20256
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:50.667606+00:00
-- url     : https://prove2.me/submissions/05a7e779-e3a1-4e8a-ba33-3a04dff933cc

/- Source: InternLM Lean-Workbook, record lean_workbook_20256.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3) : 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27 := by
  first
  | solve
    | simp only [pow_two, pow_three, ← add_assoc]
      nlinarith
  | solve
    | simp [sq, pow_three]
      nlinarith [ha.1, ha.2.1, ha.2.2, hab]
  | solve
    | simp [pow_two, pow_three, hab]
      nlinarith [ha.1, ha.2.1, ha.2.2, hab]
  | solve
    | simp [pow_two, pow_three, ← mul_assoc]
      nlinarith [ha.1, ha.2.1, ha.2.2, hab]
  | solve
    | simp [pow_two, pow_three, mul_add, add_mul, mul_comm, mul_left_comm]
      nlinarith
  | solve
    | simp [pow_two, pow_three, ← le_sub_iff_add_le, sub_nonneg, mul_nonneg]
      nlinarith [ha, hab]

example : (∀ (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3), 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27) := @solution
#print axioms solution
