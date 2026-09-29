-- Prove2me | solution 1 for WorkbookSource.problem_40020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:50.829372+00:00
-- url     : https://prove2.me/submissions/b8aef99d-b2cc-46a9-aff2-2f8679c2000f

/- InternLM Lean-Workbook, lean_workbook_40020, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x1 x2 : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < x1 ∧ 0 < x2)
  (h₁ : x1 > x2)
  (h₂ : f x1 - f x2 = x1 - x2 + (1 / x1 - 1 / x2)) :
  f x1 - f x2 = (x1 - x2) * (x1 * x2 - 1) / (x1 * x2)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [h₂]
      field_simp [h₀.1.ne', h₀.2.ne', h₁.ne]
      ring_nf
example : (∀ (x1 x2 : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < x1 ∧ 0 < x2)
  (h₁ : x1 > x2)
  (h₂ : f x1 - f x2 = x1 - x2 + (1 / x1 - 1 / x2)), f x1 - f x2 = (x1 - x2) * (x1 * x2 - 1) / (x1 * x2)) := @solution
#print axioms solution
