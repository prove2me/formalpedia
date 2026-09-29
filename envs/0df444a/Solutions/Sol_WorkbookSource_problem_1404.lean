-- Prove2me | solution 1 for WorkbookSource.problem_1404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:59.319441+00:00
-- url     : https://prove2.me/submissions/e0cb52d2-d044-47eb-a1c1-e661990990a0

/- InternLM Lean-Workbook, lean_workbook_1404, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      linarith
      constructor
      linarith
      linarith [hab, hbc, hca]
  | solve
    | constructor
      linarith [hab]
      constructor
      linarith [hbc]
      linarith [hca]
  | solve
    | constructor
      linarith
      constructor
      linarith
      linarith only [hab, hbc, hca]
  | solve
    | simp only [add_comm] at *
      constructor
      linarith
      constructor <;> linarith
  | solve
    | constructor
      nlinarith
      constructor
      nlinarith
      nlinarith [hab, hbc, hca]
  | solve
    | constructor
      nlinarith [hab]
      constructor
      nlinarith [hbc]
      nlinarith [hca]
  | solve
    | constructor
      nlinarith
      constructor
      nlinarith
      nlinarith only [hab, hbc, hca]
  | solve
    | simp only [add_comm] at *
      constructor
      nlinarith
      constructor <;> nlinarith
example : (∀ (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b), a > 0 ∧ b > 0 ∧ c > 0) := @solution
#print axioms solution
