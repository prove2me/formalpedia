-- Prove2me | solution 1 for ToricMemory.eq_61
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:18:58.938025+00:00
-- url     : https://prove2.me/submissions/73f7afe9-9c77-4d54-b330-119c27650d80

import Mathlib
import Definitions.Def_ToricMemory_CubicSAW

namespace Aux_TM61

theorem le_one (m x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / (4 * m ^ 2)) :
    Real.sqrt (4 * m ^ 2 * x) ≤ 1 := by
  rw [Real.sqrt_le_one]
  rcases (sq_nonneg m).eq_or_lt with h | h
  · rw [← h]; simp
  · have h4 : 0 < 4 * m ^ 2 := by positivity
    rw [lt_div_iff₀ h4] at hx
    linarith

end Aux_TM61

open ToricMemory Aux_TM61 in
theorem solution (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp : p * (1 - p) < 1 / (4 * mu3 ^ 2)) (hq : q * (1 - q) < 1 / (4 * mu3 ^ 2))
    (L H V : ℕ) (hH : L ≤ H) :
    Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H * Real.sqrt (4 * mu3 ^ 2 * (q * (1 - q))) ^ V ≤
      Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ L := by
  have ha1 := le_one mu3 (p * (1 - p)) (mul_nonneg hp0 (by linarith)) hp
  have hb1 := le_one mu3 (q * (1 - q)) (mul_nonneg hq0 (by linarith)) hq
  have ha0 := Real.sqrt_nonneg (4 * mu3 ^ 2 * (p * (1 - p)))
  have hb0 := Real.sqrt_nonneg (4 * mu3 ^ 2 * (q * (1 - q)))
  have hbV : Real.sqrt (4 * mu3 ^ 2 * (q * (1 - q))) ^ V ≤ 1 := pow_le_one₀ hb0 hb1
  have haH : Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H ≤
      Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ L := pow_le_pow_of_le_one ha0 ha1 hH
  have haH0 : 0 ≤ Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H := pow_nonneg ha0 H
  calc Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H * Real.sqrt (4 * mu3 ^ 2 * (q * (1 - q))) ^ V
      ≤ Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H * 1 := mul_le_mul_of_nonneg_left hbV haH0
    _ ≤ Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ L := by rw [mul_one]; exact haH
