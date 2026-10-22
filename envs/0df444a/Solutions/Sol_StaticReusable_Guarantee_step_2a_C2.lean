-- Prove2me | solution 1 for StaticReusable.Guarantee.step_2a_C2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:19:17.680325+00:00
-- url     : https://prove2.me/submissions/ca2f39c7-89af-48b4-8355-b7950f7cb269

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting
set_option autoImplicit false

open StaticReusable.Guarantee

theorem solution (z : ℕ → ℝ) (hz1 : 0 ≤ z 1) (hz2 : 0 ≤ z 2) :
    R 2 z = (z 1 ^ 2 + 4 * z 1 * z 2 + 3 * z 1 + 4 * z 2 ^ 2 + 6 * z 2 + 2) /
        (z 1 ^ 2 + 4 * z 1 * z 2 + 2 * z 1 + 5 * z 2 ^ 2 + 6 * z 2 + 2) ∧
      (4 / 5 : ℝ) ≤ R 2 z := by
  have hR : R 2 z = (z 1 ^ 2 + 4 * z 1 * z 2 + 3 * z 1 + 4 * z 2 ^ 2 + 6 * z 2 + 2) /
        (z 1 ^ 2 + 4 * z 1 * z 2 + 2 * z 1 + 5 * z 2 ^ 2 + 6 * z 2 + 2) := by
    unfold R uSum xSum a zExt
    simp [Finset.sum_range_succ, Nat.descFactorial, Finset.sum_Icc_succ_top]
    have h1 : (2 * z 2 + 2) ≠ 0 := by positivity
    have h2 : (z 1 ^ 2 + 4 * z 1 * z 2 + 2 * z 1 + 5 * z 2 ^ 2 + 6 * z 2 + 2) ≠ 0 := by positivity
    have h3 : (((2 * z 1 + 2 * z 2) / (2 * z 2 + 2)) ^ 2 + 2 * ((2 * z 1 + 2 * z 2) / (2 * z 2 + 2)) + 2) ≠ 0 := by positivity
    rw [div_eq_div_iff (mul_ne_zero h1 h3) h2]
    field_simp
    ring
  refine ⟨hR, ?_⟩
  rw [hR, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hz1 hz2, sq_nonneg (z 1), sq_nonneg (z 2)]
