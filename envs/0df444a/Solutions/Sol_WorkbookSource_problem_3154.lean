-- Prove2me | solution 1 for WorkbookSource.problem_3154
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:05.676409+00:00
-- url     : https://prove2.me/submissions/cb5fc09c-dada-44eb-8034-049c1e649ff1

/- InternLM Lean-Workbook, lean_workbook_3154, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (u v : ℝ) (hu : 1 / 2 ≤ u ∧ u ≤ 1) (hv : 1 / 2 ≤ v ∧ v ≤ 1) : 5 * (u^2 + v^2 + 1) ≤ 6 * (u + v + u * v)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | repeat rw [sq]; nlinarith
  | solve
    | repeat nlinarith [hu.1, hu.2, hv.1, hv.2]
  | solve
    | simp [hu, hv, mul_add, add_mul, mul_comm, mul_left_comm]
      nlinarith
  | solve
    | apply le_of_sub_nonneg
      simp [hu, hv]
      ring_nf
      nlinarith [hu.1, hu.2, hv.1, hv.2]
example : (∀ (u v : ℝ) (hu : 1 / 2 ≤ u ∧ u ≤ 1) (hv : 1 / 2 ≤ v ∧ v ≤ 1), 5 * (u^2 + v^2 + 1) ≤ 6 * (u + v + u * v)) := @solution
#print axioms solution
