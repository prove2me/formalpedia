-- Prove2me | solution 1 for WorkbookSource.problem_51944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:05.094202+00:00
-- url     : https://prove2.me/submissions/420ea82f-95c7-47a7-aa96-c8d7be3e15f4

/- InternLM Lean-Workbook, lean_workbook_51944, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (p q : ℝ) (hp : 3 / 2 < p ∧ p < 2) (hq : q = 1 - p) : (3 / 2 < p ∧ p < 2 ∧ 1 - q - 2 * (5 * p^2 * q - p^4 - 4 * q^2) / (6 * p) ≥ 0) ∨ (4 * (5 / 8 * p^2 + 3 / 8 * p - q)^2 - 3 / 16 * p * (p - 1) * (3 * p^2 + 13 * p + 16) ≥ 0)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | subst hq
      obtain ⟨hp1, hp2⟩ := hp
      right
      nlinarith
  | solve
    | refine' Or.inr _
      field_simp [hq]
      ring_nf at hp ⊢
      norm_num at hp ⊢
      nlinarith
  | solve
    | refine' Or.inr _
      field_simp [hq]
      ring_nf
      norm_cast
      nlinarith [hp.1, hp.2, hq]
example : (∀ (p q : ℝ) (hp : 3 / 2 < p ∧ p < 2) (hq : q = 1 - p), (3 / 2 < p ∧ p < 2 ∧ 1 - q - 2 * (5 * p^2 * q - p^4 - 4 * q^2) / (6 * p) ≥ 0) ∨ (4 * (5 / 8 * p^2 + 3 / 8 * p - q)^2 - 3 / 16 * p * (p - 1) * (3 * p^2 + 13 * p + 16) ≥ 0)) := @solution
#print axioms solution
