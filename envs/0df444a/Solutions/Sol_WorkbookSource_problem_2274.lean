-- Prove2me | solution 1 for WorkbookSource.problem_2274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:00.894075+00:00
-- url     : https://prove2.me/submissions/6d028b0a-2556-4f47-9897-063608b9b905

/- InternLM Lean-Workbook, lean_workbook_2274, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x))  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | contrapose!
      intro _
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
  | solve
    | by_contra!
      have h₁ := Int.floor_le x
      have h₂ := Int.lt_floor_add_one x
      nlinarith
  | solve
    | by_contra h
      have h₁ := Int.floor_le x
      have h₂ := Int.lt_floor_add_one x
      nlinarith
  | solve
    | rw [← add_neg_eq_zero]
      intro h
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x, h]
example : (∀ (x : ℝ) (hx : 0 < x), ¬ (x + 2022 = Int.floor x * (x - Int.floor x))) := @solution
#print axioms solution
