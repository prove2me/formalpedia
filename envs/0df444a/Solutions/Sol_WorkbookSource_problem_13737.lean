-- Prove2me | solution 1 for WorkbookSource.problem_13737
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:28.411253+00:00
-- url     : https://prove2.me/submissions/c89f7d74-1250-40c6-985b-917c25be184f

/- InternLM Lean-Workbook, lean_workbook_13737, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x1 x2 x3 x4 x5 : ℝ) : x1 + x2 + x3 = 3 ∧ x2 + x3 + x4 = 3 ∧ x3 + x4 + x5 = 3 ∧ x4 + x5 + x1 = 3 ∧ x5 + x1 + x2 = 3 ↔ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      linarith only [h1, h2, h3, h4, h5]
      linarith only [h1, h2, h3, h4, h5]
      linarith only [h1, h2, h3, h4, h5]
      linarith only [h1, h2, h3, h4, h5]
      linarith only [h1, h2, h3, h4, h5]
      rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | solve
    | constructor
      rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      nlinarith only [h1, h2, h3, h4, h5]
      nlinarith only [h1, h2, h3, h4, h5]
      nlinarith only [h1, h2, h3, h4, h5]
      nlinarith only [h1, h2, h3, h4, h5]
      nlinarith only [h1, h2, h3, h4, h5]
      rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
example : (∀ (x1 x2 x3 x4 x5 : ℝ), x1 + x2 + x3 = 3 ∧ x2 + x3 + x4 = 3 ∧ x3 + x4 + x5 = 3 ∧ x4 + x5 + x1 = 3 ∧ x5 + x1 + x2 = 3 ↔ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) := @solution
#print axioms solution
