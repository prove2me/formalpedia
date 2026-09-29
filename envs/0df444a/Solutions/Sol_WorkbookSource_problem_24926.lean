-- Prove2me | solution 1 for WorkbookSource.problem_24926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:35.320401+00:00
-- url     : https://prove2.me/submissions/997094cb-f7da-4a63-abab-11dd10a63695

/- InternLM Lean-Workbook, lean_workbook_24926, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + y + z = 1 / 2) :
  x^2 + y^2 + z^2 < 1 / 4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [h₁, h₀]
  | solve
    | have h₀' : 0 < x + y + z := by linarith
      nlinarith
  | solve
    | have h₂ : x + y + z > 0 := by linarith
      nlinarith [h₁]
  | solve
    | have h₂ : 0 < x + y + z := by linarith
      nlinarith [h₁]
example : (∀ (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + y + z = 1 / 2), x^2 + y^2 + z^2 < 1 / 4) := @solution
#print axioms solution
