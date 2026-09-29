-- Prove2me | solution 1 for WorkbookSource.problem_25211
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:37.284631+00:00
-- url     : https://prove2.me/submissions/2ff14bab-f8a4-4f17-96b0-bb5be79e91c8

/- InternLM Lean-Workbook, lean_workbook_25211, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (hab : a * b > 0) (hbc : b * c > 0) (hca : c * a > 0) : a * b + b * c + c * a > 0 ∧ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) > 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> positivity
  | solve
    | refine' ⟨_, _⟩
      linarith
      positivity
  | solve
    | refine ⟨add_pos (add_pos hab hbc) hca,?_⟩
      positivity
  | solve
    | constructor
      linarith only [hab, hbc, hca]
      positivity
  | solve
    | refine' ⟨_, _⟩
      nlinarith
      positivity
  | solve
    | constructor
      nlinarith only [hab, hbc, hca]
      positivity
example : (∀ (a b c : ℝ) (hab : a * b > 0) (hbc : b * c > 0) (hca : c * a > 0), a * b + b * c + c * a > 0 ∧ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) > 0) := @solution
#print axioms solution
