-- Prove2me | solution 1 for WorkbookSource.problem_39005
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:49.026977+00:00
-- url     : https://prove2.me/submissions/aa7dc046-d1a9-4a35-9832-1f24a9d9d2d1

/- InternLM Lean-Workbook, lean_workbook_39005, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x : ℝ, (6 * x ^ 2 - x ^ 3) / 8 - x = (x * (x - 2) * (4 - x)) / 8 ∧ 4 - (6 * x ^ 2 - x ^ 3) / 8 = ((4 - x) ^ 2 * (2 + x)) / 8  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro x
      constructor <;> ring
  | solve
    | intro x
      exact ⟨by ring, by ring⟩
  | solve
    | refine' fun x => ⟨_, _⟩ <;> ring
  | solve
    | intro x
      apply And.intro <;> ring
example : (∀ x : ℝ, (6 * x ^ 2 - x ^ 3) / 8 - x = (x * (x - 2) * (4 - x)) / 8 ∧ 4 - (6 * x ^ 2 - x ^ 3) / 8 = ((4 - x) ^ 2 * (2 + x)) / 8) := @solution
#print axioms solution
