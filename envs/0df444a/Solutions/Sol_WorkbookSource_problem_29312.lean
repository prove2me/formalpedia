-- Prove2me | solution 1 for WorkbookSource.problem_29312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:16.028931+00:00
-- url     : https://prove2.me/submissions/326c5490-e1b2-44cf-b5c9-07b7f23d5464

/- InternLM Lean-Workbook, lean_workbook_29312, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y t : ℝ) (hx: x ≠ 0 ∧ y ≠ 0) (h : t = x/y + y/x) :  t^2 - 2 + 4 ≥ 3 * t ↔ (t - 1) * (t - 2) ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [h, hx]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | constructor <;> intro h1 <;> nlinarith [h, hx.1, hx.2, h1]
  | solve
    | constructor <;> intro h1
      nlinarith
      nlinarith [hx.1, hx.2, h]
  | solve
    | constructor
      intro h1
      linarith
      intro h1
      linarith [hx.1, hx.2, h]
  | solve
    | simp [h, hx]
      ring_nf
      constructor <;> intro h <;> nlinarith
  | solve
    | constructor
      intro h1
      nlinarith
      intro h1
      nlinarith [hx.1, hx.2, h]
example : (∀ (x y t : ℝ) (hx: x ≠ 0 ∧ y ≠ 0) (h : t = x/y + y/x), t^2 - 2 + 4 ≥ 3 * t ↔ (t - 1) * (t - 2) ≥ 0) := @solution
#print axioms solution
