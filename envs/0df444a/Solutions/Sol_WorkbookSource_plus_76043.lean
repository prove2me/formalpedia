-- Prove2me | solution 1 for WorkbookSource.plus_76043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:45.27895+00:00
-- url     : https://prove2.me/submissions/595559df-5294-4aed-9051-8a4a2319bb1f

/- InternLM Lean-Workbook, lean_workbook_plus_76043, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf: f = fun x => if x ≤ 1/2 then 1 else 0) : ¬ (∃ x, f x = x)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [hf]
      push_neg
      intro x
      split_ifs <;> linarith
  | solve
    | simp only [hf]
      push_neg
      intro x
      split_ifs <;> linarith
  | solve
    | rw [hf]
      push_neg
      intro x hx
      split_ifs at hx <;> linarith
  | solve
    | rw [hf]
      push_neg
      intro x
      split_ifs <;> intro h <;> linarith
  | solve
    | rw [hf]
      push_neg
      intro x
      split_ifs <;> nlinarith
  | solve
    | simp only [hf]
      push_neg
      intro x
      split_ifs <;> nlinarith
  | solve
    | rw [hf]
      push_neg
      intro x hx
      split_ifs at hx <;> nlinarith
  | solve
    | rw [hf]
      push_neg
      intro x
      split_ifs <;> intro h <;> nlinarith
example : (∀ (f : ℝ → ℝ) (hf: f = fun x => if x ≤ 1/2 then 1 else 0), ¬ (∃ x, f x = x)) := @solution
#print axioms solution
