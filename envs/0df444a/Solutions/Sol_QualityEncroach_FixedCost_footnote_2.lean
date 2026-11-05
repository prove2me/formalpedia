-- Prove2me | solution 1 for QualityEncroach.FixedCost.footnote_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:34:36.886742+00:00
-- url     : https://prove2.me/submissions/c322c8e8-8b95-4b97-bbbe-d8428691c72c

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

open QualityEncroach.FixedCost in
theorem solution (t : ℝ) (ht : 1 ≤ t) : QualityEncroach.FixedCost.h1 t < 0 := by
  unfold h1 h11 h12
  set S := 20 * t ^ 2 - 16 * t + 1 with hS
  have hSpos : 0 < S := by nlinarith
  set s := Real.sqrt S with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = S := Real.sq_sqrt hSpos.le
  set p := 12800 * t ^ 7 - 14720 * t ^ 6 + 3584 * t ^ 5 + 9616 * t ^ 4 - 13664 * t ^ 3 +
    6880 * t ^ 2 - 1200 * t + 25 with hp
  set H := -256000 * t ^ 9 + 1036800 * t ^ 8 - 1600960 * t ^ 7 + 1345728 * t ^ 6 -
    614112 * t ^ 5 + 50896 * t ^ 4 + 88612 * t ^ 3 - 36540 * t ^ 2 + 4200 * t - 75 with hH
  -- `p > 0` on `t ≥ 1`
  have hppos : 0 < p := by
    obtain ⟨x, hx0, rfl⟩ : ∃ x, 0 ≤ x ∧ t = 1 + x := ⟨t - 1, by linarith, by ring⟩
    have e : p = 12800 * x ^ 7 + 74880 * x ^ 6 + 184064 * x ^ 5 + 254736 * x ^ 4 +
        214240 * x ^ 3 + 107424 * x ^ 2 + 29232 * x + 3321 := by rw [hp]; ring
    rw [e]; positivity
  have goal_form : -3 * p = -3 * (12800 * t ^ 7 - 14720 * t ^ 6 + 3584 * t ^ 5 +
      9616 * t ^ 4 - 13664 * t ^ 3 + 6880 * t ^ 2 - 1200 * t + 25) := by rw [hp]
  rw [← goal_form]
  rcases le_total 2 t with h2 | h2
  · -- `t ≥ 2`: the polynomial part is already negative
    have hHneg : H < 0 := by
      obtain ⟨y, hy0, rfl⟩ : ∃ y, 0 ≤ y ∧ t = 2 + y := ⟨t - 2, by linarith, by ring⟩
      have e : H = -(256000 * y ^ 9 + 3571200 * y ^ 8 + 21876160 * y ^ 7 + 76978112 * y ^ 6 +
          170555616 * y ^ 5 + 244591344 * y ^ 4 + 223600220 * y ^ 3 + 121985124 * y ^ 2 +
          33570008 * y + 2713675) := by rw [hH]; ring
      rw [e]
      have : 0 < 256000 * y ^ 9 + 3571200 * y ^ 8 + 21876160 * y ^ 7 + 76978112 * y ^ 6 +
          170555616 * y ^ 5 + 244591344 * y ^ 4 + 223600220 * y ^ 3 + 121985124 * y ^ 2 +
          33570008 * y + 2713675 := by positivity
      linarith
    have : 0 ≤ p * s := mul_nonneg hppos.le hs0
    linarith
  · -- `1 ≤ t ≤ 2`: compare squares
    have hG : 102400 * t ^ 8 - 501760 * t ^ 7 + 813056 * t ^ 6 - 635072 * t ^ 5 +
        206212 * t ^ 4 + 93048 * t ^ 3 - 115260 * t ^ 2 + 32250 * t - 675 < 0 := by
      obtain ⟨x, hx0, rfl⟩ : ∃ x, 0 ≤ x ∧ t = 1 + x := ⟨t - 1, by linarith, by ring⟩
      have hx1 : x ≤ 1 := by linarith
      have e : 102400 * (1 + x) ^ 8 - 501760 * (1 + x) ^ 7 + 813056 * (1 + x) ^ 6 -
          635072 * (1 + x) ^ 5 + 206212 * (1 + x) ^ 4 + 93048 * (1 + x) ^ 3 -
          115260 * (1 + x) ^ 2 + 32250 * (1 + x) - 675 =
          102400 * x ^ 8 + 317440 * x ^ 7 + 167936 * x ^ 6 - 559296 * x ^ 5 -
          1166908 * x ^ 4 - 998904 * x ^ 3 - 423484 * x ^ 2 - 84422 * x - 5801 := by ring
      rw [e]
      have h85 : x ^ 8 ≤ x ^ 5 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
      have h75 : x ^ 7 ≤ x ^ 5 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
      have h65 : x ^ 6 ≤ x ^ 5 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
      have h54 : x ^ 5 ≤ x ^ 4 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
      have h3 : 0 ≤ x ^ 3 := by positivity
      have h2' : 0 ≤ x ^ 2 := by positivity
      have h4 : 0 ≤ x ^ 4 := by positivity
      nlinarith
    have hF : 9 * p ^ 2 * S - H ^ 2 =
        -4 * t ^ 2 * (20 * t ^ 2 - 16 * t + 5) ^ 4 *
        (102400 * t ^ 8 - 501760 * t ^ 7 + 813056 * t ^ 6 - 635072 * t ^ 5 +
        206212 * t ^ 4 + 93048 * t ^ 3 - 115260 * t ^ 2 + 32250 * t - 675) := by
      rw [hp, hH, hS]; ring
    have hpos : 0 < 4 * t ^ 2 * (20 * t ^ 2 - 16 * t + 5) ^ 4 := by
      have : 0 < 20 * t ^ 2 - 16 * t + 5 := by nlinarith
      have : 0 < t := by linarith
      positivity
    have hlt : H ^ 2 < (3 * p * s) ^ 2 := by
      have : (3 * p * s) ^ 2 = 9 * p ^ 2 * S := by rw [← hs2]; ring
      rw [this]
      nlinarith [mul_pos hpos (neg_pos.mpr hG)]
    have habs := abs_lt_of_sq_lt_sq hlt (by positivity)
    have := le_abs_self H
    linarith
