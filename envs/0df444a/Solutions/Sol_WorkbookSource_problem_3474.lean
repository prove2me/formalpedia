-- Prove2me | solution 1 for WorkbookSource.problem_3474
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:07.255596+00:00
-- url     : https://prove2.me/submissions/d2ae6ec0-2cd2-4e86-b8b1-1a53f2bde9e6

/- InternLM Lean-Workbook, lean_workbook_3474, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (s₁ : ℝ) (s₃ : ℝ) : s₃ ≥ 1 ∧ s₁ ≥ 3 → 3 * (5 * s₁ - 3) * (s₁ - 3) ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro h
      nlinarith [h]
  | solve
    | intro h
      nlinarith [h.2]
  | solve
    | rintro ⟨h3, h4⟩
      nlinarith
  | solve
    | intro h
      repeat' nlinarith
example : (∀ (s₁ : ℝ) (s₃ : ℝ), s₃ ≥ 1 ∧ s₁ ≥ 3 → 3 * (5 * s₁ - 3) * (s₁ - 3) ≥ 0) := @solution
#print axioms solution
