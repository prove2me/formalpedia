-- Prove2me | solution 1 for WorkbookSource.problem_20573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:51:58.877038+00:00
-- url     : https://prove2.me/submissions/2ca6ca48-0ef7-41df-8240-5c98d7de6553

/- InternLM Lean-Workbook, lean_workbook_20573, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (y : ℝ) (h₁ : 1 < y) : y^2 + 1 > y^2 ∧ y^2 > y  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | apply And.intro
      linarith
      nlinarith
  | solve
    | constructor <;> nlinarith only [h₁]
  | solve
    | constructor <;> nlinarith [sq_nonneg y]
  | solve
    | constructor
      nlinarith [h₁]
      nlinarith [h₁]
example : (∀ (y : ℝ) (h₁ : 1 < y), y^2 + 1 > y^2 ∧ y^2 > y) := @solution
#print axioms solution
