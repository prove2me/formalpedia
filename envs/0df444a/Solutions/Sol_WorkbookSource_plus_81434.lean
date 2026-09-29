-- Prove2me | solution 1 for WorkbookSource.plus_81434
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:47.003624+00:00
-- url     : https://prove2.me/submissions/7b56299d-9dcf-41a8-91ae-dbf64c5a6f0c

/- InternLM Lean-Workbook, lean_workbook_plus_81434, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (hx: a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)) : ¬(a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | contrapose! hx
      nlinarith
  | solve
    | contrapose! hx
      nlinarith [hx]
  | solve
    | rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
      nlinarith
  | solve
    | rintro ⟨ha, hb, hc, hab, hbc, hca⟩
      nlinarith
example : (∀ (a b c : ℝ) (hx: a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)), ¬(a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a)) := @solution
#print axioms solution
