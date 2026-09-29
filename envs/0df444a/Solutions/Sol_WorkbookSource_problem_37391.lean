-- Prove2me | solution 1 for WorkbookSource.problem_37391
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:40.620284+00:00
-- url     : https://prove2.me/submissions/4159af6a-dab0-439b-b77f-fd531b2fe68c

/- InternLM Lean-Workbook, lean_workbook_37391, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c : ℝ} (hx: a >= 0 ∧ b >= 0 ∧ c >= 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + c - b) / (2 * (a + b + c) * (c + a)) ≥ 0  := by
  first
  | solve
    | apply div_nonneg
      · linarith
      · positivity
  | solve
    | refine' div_nonneg _ _
      linarith[hab, hbc, hca]
      nlinarith [hx.1, hx.2.1, hx.2.2, hab, hbc, hca]
  | solve
    | refine' div_nonneg (by nlinarith) (by nlinarith)
  | solve
    | refine' div_nonneg (by linarith) (by nlinarith)
  | solve
    | apply div_nonneg
      nlinarith [hx.1, hx.2.1, hx.2.2, hab, hbc, hca]
      nlinarith [hx.1, hx.2.1, hx.2.2, hab, hbc, hca]
  | solve
    | apply div_nonneg
      linarith [hx.1, hx.2.1, hx.2.2]
      nlinarith [hx.1, hx.2.1, hx.2.2, hab, hbc, hca]
  | solve
    | apply div_nonneg
      linarith
      nlinarith only [hx.1, hx.2.1, hx.2.2, hab, hbc, hca]
  | solve
    | exact div_nonneg (sub_nonneg.mpr (by linarith [hx.1, hx.2.1, hab, hbc, hca]))
        (mul_nonneg (by linarith [hx.1, hx.2.1, hab, hbc, hca]) (by linarith [hx.1, hx.2.1, hab, hbc, hca]))
example : (∀ {a b c : ℝ} (hx: a >= 0 ∧ b >= 0 ∧ c >= 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b), (a + c - b) / (2 * (a + b + c) * (c + a)) ≥ 0) := @solution
#print axioms solution
