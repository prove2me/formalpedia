-- Prove2me | solution 1 for WorkbookSource.problem_28159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:14.823632+00:00
-- url     : https://prove2.me/submissions/c8e637a1-7757-437b-bfe7-ae378c7936ea

/- InternLM Lean-Workbook, lean_workbook_28159, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a : ℝ)
  (h₀ : 0 < a) :
  16 * (a + 1)^2 + 16 ≤ (a + 1)^4 + 32 * (a + 1)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [sq_nonneg (a + 1 - 2)]
  | solve
    | rw [add_comm]
      nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
  | solve
    | have h₁ := sq_nonneg (a + 1)
      have h₂ := sq_nonneg (a - 1)
      nlinarith [h₀, h₁, h₂]
  | solve
    | have h₁ := sq_nonneg (a + 1 - 2)
      have h₂ := sq_nonneg (a + 1 + 2)
      nlinarith [h₁, h₂]
example : (∀ (a : ℝ)
  (h₀ : 0 < a), 16 * (a + 1)^2 + 16 ≤ (a + 1)^4 + 32 * (a + 1)) := @solution
#print axioms solution
