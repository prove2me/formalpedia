-- Prove2me | solution 1 for WorkbookSource.problem_6918
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:16.13179+00:00
-- url     : https://prove2.me/submissions/4fcbe9ce-2a5e-4f82-9ad9-b2a465d831f7

/- InternLM Lean-Workbook, lean_workbook_6918, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (1 + a) + 1 / (1 + b^2) = 1) : a + 2 * b ≥ 3  := by
  have hn1 : 1+a ≠ 0 := ne_of_gt (by positivity)
  have hn2 : 1+b^2 ≠ 0 := ne_of_gt (by positivity)
  have hprod : a*b^2=1 := by
    field_simp [hn1,hn2] at hab
    nlinarith [hab]
  have hsq : 0 ≤ (b-1)^2*(2*b+1) := mul_nonneg (sq_nonneg _) (by positivity)
  by_contra! hlt
  have hneg : (a+2*b-3)*b^2<0 := mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hb)
  nlinarith [hsq,hprod]

example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (1 + a) + 1 / (1 + b^2) = 1), a + 2 * b ≥ 3) := @solution
#print axioms solution
