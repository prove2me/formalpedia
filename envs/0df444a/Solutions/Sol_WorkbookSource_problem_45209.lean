-- Prove2me | solution 1 for WorkbookSource.problem_45209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:11.612588+00:00
-- url     : https://prove2.me/submissions/ea24c4fe-f2a5-43c2-9c79-4417d707705d

/- InternLM Lean-Workbook, lean_workbook_45209, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3) : a ^ 2 + b ^ 2 + c ^ 3 ≤ 27  := by
  first
  | solve
    | rcases ha with ⟨ha,hb,hc⟩
      have hc3 : c ≤ 3 := by linarith
      have hca := mul_nonneg ha (show 0 ≤ 3-a by linarith)
      have hcb := mul_nonneg hb (show 0 ≤ 3-b by linarith)
      have hcc := mul_nonneg hc (show 0 ≤ 3-c by linarith)
      have hcc2 := mul_nonneg hc (show 0 ≤ 9-c^2 by nlinarith)
      nlinarith
  | solve
    | simp only [pow_two, pow_three, ← add_assoc]
      nlinarith
  | solve
    | simp [sq, pow_two, pow_three, add_assoc, add_comm, add_left_comm]
      nlinarith [ha.1, ha.2.1, ha.2.2, hab]
  | solve
    | simp only [pow_two, pow_three]
      nlinarith
  | solve
    | simp [pow_two, pow_three, mul_assoc]
      nlinarith [ha.1, ha.2.1, ha.2.2, hab]
  | solve
    | simp only [pow_two, pow_three]
      nlinarith [ha, hab]
example : (∀ (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3), a ^ 2 + b ^ 2 + c ^ 3 ≤ 27) := @solution
#print axioms solution
