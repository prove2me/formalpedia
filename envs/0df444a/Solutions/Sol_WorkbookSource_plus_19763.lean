-- Prove2me | solution 1 for WorkbookSource.plus_19763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:10.621864+00:00
-- url     : https://prove2.me/submissions/5adf01cc-84e8-4a9e-b4bf-4ec9169a48fd

/- InternLM Lean-Workbook, lean_workbook_plus_19763, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1) :
  a^3 + b^3 + c^3 ≤ 3 * (1 + a * b * c)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have : a = 1 - b - c := by linarith
      simp [this]
      nlinarith
example : (∀ (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1), a^3 + b^3 + c^3 ≤ 3 * (1 + a * b * c)) := @solution
#print axioms solution
