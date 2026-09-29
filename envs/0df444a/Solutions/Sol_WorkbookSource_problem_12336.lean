-- Prove2me | solution 1 for WorkbookSource.problem_12336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:28.545049+00:00
-- url     : https://prove2.me/submissions/a6049a00-c32a-43e7-9804-c07009235051

/- InternLM Lean-Workbook, lean_workbook_12336, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c d e f : ℝ)
  (h₀ : a + b + c = d + e + f)
  (h₁ : 4 * a + 2 * b + c = 4 * d + 2 * e + f)
  (h₂ : 9 * a + 3 * b + c = 9 * d + 3 * e + f) :
  a = d ∧ b = e ∧ c = f  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | refine' ⟨_, _, _⟩
      repeat' linarith
  | solve
    | refine ⟨?_,?_,?_⟩
      linarith
      linarith
      linarith
  | solve
    | refine' ⟨_, _, _⟩
      all_goals linarith [h₀, h₁, h₂]
  | solve
    | refine ⟨?_,?_,?_⟩
      linarith
      linarith
      linarith [h₀, h₁, h₂]
  | solve
    | refine' ⟨_, _, _⟩
      repeat' nlinarith
  | solve
    | refine ⟨?_,?_,?_⟩
      nlinarith
      nlinarith
      nlinarith
  | solve
    | refine' ⟨_, _, _⟩
      all_goals nlinarith [h₀, h₁, h₂]
  | solve
    | refine ⟨?_,?_,?_⟩
      nlinarith
      nlinarith
      nlinarith [h₀, h₁, h₂]
example : (∀ (a b c d e f : ℝ)
  (h₀ : a + b + c = d + e + f)
  (h₁ : 4 * a + 2 * b + c = 4 * d + 2 * e + f)
  (h₂ : 9 * a + 3 * b + c = 9 * d + 3 * e + f), a = d ∧ b = e ∧ c = f) := @solution
#print axioms solution
