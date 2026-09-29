-- Prove2me | solution 1 for WorkbookSource.problem_2545
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:02.467168+00:00
-- url     : https://prove2.me/submissions/87bd7e7c-901f-47d2-804c-a69340db87d3

/- InternLM Lean-Workbook, lean_workbook_2545, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : x^2 - 3*x - 1 = 0) : 2*x^3 - 3*x^2 - 11*x + 8 = 11  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num
      nlinarith [hx]
  | solve
    | field_simp [sq, hx]
      nlinarith
  | solve
    | ring_nf at hx
      ring_nf
      nlinarith
  | solve
    | field_simp [sq] at hx ⊢
      nlinarith
example : (∀ (x : ℝ) (hx : x^2 - 3*x - 1 = 0), 2*x^3 - 3*x^2 - 11*x + 8 = 11) := @solution
#print axioms solution
