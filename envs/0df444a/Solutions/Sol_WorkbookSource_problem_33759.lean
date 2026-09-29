-- Prove2me | solution 1 for WorkbookSource.problem_33759
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:47.819374+00:00
-- url     : https://prove2.me/submissions/49f8d8d3-11c7-453f-9021-b57981723dc2

/- InternLM Lean-Workbook, lean_workbook_33759, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a : ℝ) (h : a > -1) : (a + 1)^3 ≥ 0  := by
  first
  | solve
    | have h0 : 0 ≤ a+1 := by linarith
      exact pow_nonneg h0 3
  | solve
    | have : a + 1 > 0 := by linarith
      positivity
  | solve
    | apply pow_nonneg
      nlinarith
  | solve
    | apply pow_nonneg
      exact le_of_lt (by linarith)
  | solve
    | obtain ⟨a, rfl⟩ : ∃ a', a = a' := ⟨a, rfl⟩
      simp [pow_three]
      nlinarith
  | solve
    | rw [pow_succ]
      nlinarith
  | solve
    | have h1 := sq_nonneg (a + 1)
      nlinarith
  | solve
    | field_simp [pow_three]
      nlinarith [h]
  | solve
    | refine' pow_nonneg _ 3
      linarith [h]
  | solve
    | have h1 : a + 1 ≥ 0 := by linarith
      exact pow_nonneg h1 3
example : (∀ (a : ℝ) (h : a > -1), (a + 1)^3 ≥ 0) := @solution
#print axioms solution
