-- Prove2me | solution 1 for WorkbookSource.plus_34031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:13.788264+00:00
-- url     : https://prove2.me/submissions/bee69a14-3df6-4582-a936-0a7ff9c60639

/- InternLM Lean-Workbook, lean_workbook_plus_34031, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c x : ℝ)
  (h₀ : b ≥ (a^2 + c^2) / 4) :
  x^4 + a * x^3 + b * x^2 + c * x + 1 ≥ 0   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have h₁ := sq_nonneg (x^2 + a * x / 2)
      have h₂ := sq_nonneg (c * x / 2 + 1)
      nlinarith
example : (∀ (a b c x : ℝ)
  (h₀ : b ≥ (a^2 + c^2) / 4), x^4 + a * x^3 + b * x^2 + c * x + 1 ≥ 0) := @solution
#print axioms solution
