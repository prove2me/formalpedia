-- Prove2me | solution 1 for StaticReusable.Guarantee.step_2a_C3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:48:12.806529+00:00
-- url     : https://prove2.me/submissions/632f3b91-7236-4ccc-abac-67858d39dd8b

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open StaticReusable.Guarantee

theorem solution (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 3, 0 ≤ z k) :
    (15 / 19 : ℝ) ≤ R 3 z := by
  have hz1 := hz 1 (by simp)
  have hz2 := hz 2 (by simp)
  have hz3 := hz 3 (by simp)
  set u : ℝ := 3 * z 1 + 6 * z 2 + 6 * z 3 with hu
  set x : ℝ := 3 * z 2 + 6 * z 3 + 6 with hx
  have hxpos : 0 < x := by positivity
  have hupos : 0 ≤ u := by positivity
  have hR : R 3 z = (z 1 + x) * (3 * u ^ 2 + 6 * u * x + 6 * x ^ 2) /
      (u ^ 3 + 3 * u ^ 2 * x + 6 * u * x ^ 2 + 6 * x ^ 3) := by
    unfold R uSum xSum a zExt
    simp [Finset.sum_range_succ, Nat.descFactorial, Finset.sum_Icc_succ_top]
    have h0 : (u ^ 3 + 3 * u ^ 2 * x + 6 * u * x ^ 2 + 6 * x ^ 3) ≠ 0 := by positivity
    have hu' : 3 * z 1 + 6 * z 2 + 6 * z 3 = u := rfl
    have hx' : 3 * z 2 + 6 * z 3 + 6 = x := rfl
    have hx0 : x ≠ 0 := hxpos.ne'
    rw [div_eq_div_iff (by positivity) h0]
    field_simp
    ring
  rw [hR, le_div_iff₀ (by positivity)]
  have hpoly : 19 * ((z 1 + x) * (3 * u ^ 2 + 6 * u * x + 6 * x ^ 2)) -
      15 * (u ^ 3 + 3 * u ^ 2 * x + 6 * u * x ^ 2 + 6 * x ^ 3) = 108 * z 1 ^ 3 * z 2 ^ 0 * z 3 ^ 0 + 972 * z 1 ^ 2 * z 2 ^ 1 * z 3 ^ 0 + 2322 * z 1 ^ 2 * z 2 ^ 0 * z 3 ^ 1 + 2700 * z 1 ^ 2 * z 2 ^ 0 * z 3 ^ 0 + 2214 * z 1 ^ 1 * z 2 ^ 2 * z 3 ^ 0 + 11124 * z 1 ^ 1 * z 2 ^ 1 * z 3 ^ 1 + 13392 * z 1 ^ 1 * z 2 ^ 1 * z 3 ^ 0 + 10584 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 2 + 20088 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 1 + 6696 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 0 + 5832 * z 1 ^ 0 * z 2 ^ 2 * z 3 ^ 1 + 11664 * z 1 ^ 0 * z 2 ^ 2 * z 3 ^ 0 + 14904 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 2 + 36288 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 1 + 12960 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 0 + 9720 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 3 + 28512 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 2 + 20736 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 1 + 5184 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 0 := by
    rw [hu, hx]; ring
  have hnn : 0 ≤ 108 * z 1 ^ 3 * z 2 ^ 0 * z 3 ^ 0 + 972 * z 1 ^ 2 * z 2 ^ 1 * z 3 ^ 0 + 2322 * z 1 ^ 2 * z 2 ^ 0 * z 3 ^ 1 + 2700 * z 1 ^ 2 * z 2 ^ 0 * z 3 ^ 0 + 2214 * z 1 ^ 1 * z 2 ^ 2 * z 3 ^ 0 + 11124 * z 1 ^ 1 * z 2 ^ 1 * z 3 ^ 1 + 13392 * z 1 ^ 1 * z 2 ^ 1 * z 3 ^ 0 + 10584 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 2 + 20088 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 1 + 6696 * z 1 ^ 1 * z 2 ^ 0 * z 3 ^ 0 + 5832 * z 1 ^ 0 * z 2 ^ 2 * z 3 ^ 1 + 11664 * z 1 ^ 0 * z 2 ^ 2 * z 3 ^ 0 + 14904 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 2 + 36288 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 1 + 12960 * z 1 ^ 0 * z 2 ^ 1 * z 3 ^ 0 + 9720 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 3 + 28512 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 2 + 20736 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 1 + 5184 * z 1 ^ 0 * z 2 ^ 0 * z 3 ^ 0 := by positivity
  nlinarith
