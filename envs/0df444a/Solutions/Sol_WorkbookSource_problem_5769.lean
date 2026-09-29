-- Prove2me | solution 1 for WorkbookSource.problem_5769
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:10.776732+00:00
-- url     : https://prove2.me/submissions/afc9609d-569c-47d8-b13a-f167a226234c

/- InternLM Lean-Workbook, lean_workbook_5769, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (n k : ℝ) (hn : n > 0) (hk : k ≥ (n^2)/2) : ¬∃ a b c : ℝ, a + b + c = n ∧ a * b + b * c + c * a = k  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro ⟨a, b, c, h1, h2⟩
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | rintro ⟨a, b, c, habc, abc⟩
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  | solve
    | rintro ⟨a, b, c, h1, h2⟩
      have h3 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
      nlinarith [h1, h2, h3]
  | solve
    | rintro ⟨a, b, c, h1, h2⟩
      have h3 := sq_nonneg (a-b)
      have h4 := sq_nonneg (b-c)
      have h5 := sq_nonneg (c-a)
      nlinarith
example : (∀ (n k : ℝ) (hn : n > 0) (hk : k ≥ (n^2)/2), ¬∃ a b c : ℝ, a + b + c = n ∧ a * b + b * c + c * a = k) := @solution
#print axioms solution
