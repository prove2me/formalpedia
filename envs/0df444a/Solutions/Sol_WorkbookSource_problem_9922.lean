-- Prove2me | solution 1 for WorkbookSource.problem_9922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:16.329344+00:00
-- url     : https://prove2.me/submissions/71ac158c-5287-40bc-ad5d-a568961562b2

/- InternLM Lean-Workbook, lean_workbook_9922, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d e f : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f) : a + b + c + d + e + f ≥ 6  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp only [add_comm]
      nlinarith
  | solve
    | nlinarith only [ha, hb, hc, hd, he, hf]
  | solve
    | norm_num at *
      linarith only [ha, hb, hc, hd, he, hf]
  | solve
    | apply le_of_sub_nonneg
      linarith only [ha, hb, hc, hd, he, hf]
  | solve
    | norm_num at *
      nlinarith only [ha, hb, hc, hd, he, hf]
  | solve
    | apply le_of_sub_nonneg
      nlinarith only [ha, hb, hc, hd, he, hf]
example : (∀ (a b c d e f : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f), a + b + c + d + e + f ≥ 6) := @solution
#print axioms solution
