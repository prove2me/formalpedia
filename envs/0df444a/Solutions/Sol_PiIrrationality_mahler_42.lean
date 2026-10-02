-- Prove2me | solution 1 for PiIrrationality.mahler_42
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T14:29:52.873595+00:00
-- url     : https://prove2.me/submissions/c9242a4c-a5ec-460c-897f-52186f99ab60

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_PiIrrationality_mahler_1953_eq13
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds

open PiIrrationality in
theorem solution :
    PiIrrationality.UpperBound (42 : ℝ) := by
  intro ε hε
  refine ⟨10 ^ 15, fun p q hq hQ => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqbig : (10 : ℝ) ^ 15 ≤ q := by exact_mod_cast hQ
  have hqpos : (0 : ℝ) < q := by positivity
  -- general bound: 1 / q^(42+ε) ≤ 1/q
  have hpow_ge : (q : ℝ) ≤ (q : ℝ) ^ ((42 : ℝ) + ε) := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hsmall : 1 / (q : ℝ) ^ ((42 : ℝ) + ε) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rcases le_or_gt p 0 with hp0 | hp0
  · -- nonpositive numerator
    have : (p : ℝ) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hp0) hqpos.le
    have hpi := Real.pi_gt_three
    rw [abs_of_pos (by linarith)]
    linarith
  rcases le_or_gt (4 * (q : ℤ)) p with hp4 | hp4
  · -- numerator at least 4q
    have h4 : (4 : ℝ) ≤ (p : ℝ) / q := by
      rw [le_div_iff₀ hqpos]; exact_mod_cast (by linarith : (4 : ℤ) * q ≤ p)
    have hpi := Real.pi_lt_d2
    rw [abs_of_neg (by linarith)]
    linarith
  -- main case: 0 < p < 4q
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = m := ⟨p.toNat, (Int.toNat_of_nonneg hp0.le).symm⟩
  have hm0 : 0 < m := by exact_mod_cast hp0
  have hm4 : m < 4 * q := by exact_mod_cast hp4
  set L : ℝ := Real.logb 10 q with hL
  have hqL : (10 : ℝ) ^ L = q := Real.rpow_logb (by norm_num) (by norm_num) hqpos
  have hL15 : 15 ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hqpos]
    exact_mod_cast hqbig
  set n : ℕ := ⌊10 * L / 2.9245⌋₊ + 1 with hn
  have hfl1 : 10 * L / 2.9245 < n := by
    rw [hn]; push_cast; exact Nat.lt_floor_add_one _
  have hfl2 : (n : ℝ) ≤ 10 * L / 2.9245 + 1 := by
    rw [hn]; push_cast
    have := Nat.floor_le (a := 10 * L / 2.9245) (by positivity)
    linarith
  have hn50 : 50 ≤ n := by
    have h49 : (49 : ℝ) < n := by
      have : (49 : ℝ) < 10 * L / 2.9245 := by
        rw [lt_div_iff₀ (by norm_num)]; linarith
      linarith
    have : 49 < n := by exact_mod_cast h49
    omega
  have hq10 : (q : ℝ) ^ 10 = (10 : ℝ) ^ (L * 10) := by
    rw [Real.rpow_mul (by norm_num), hqL]; norm_cast
  have hnq : (q : ℝ) ^ 10 < (10 : ℝ) ^ ((2.9245 : ℝ) * n) := by
    rw [hq10, Real.rpow_lt_rpow_left_iff (by norm_num)]
    rw [div_lt_iff₀ (by norm_num)] at hfl1
    linarith
  have key := mahler_1953_eq13 m q n hm0 hq hm4 hn50 hnq
  have hlower : 1 / (q : ℝ) ^ ((42 : ℝ) + ε) ≤
      (10 : ℝ) ^ (-((8.9101 : ℝ) * n)) / (q : ℝ) ^ 10 := by
    rw [hq10, ← hqL, ← Real.rpow_mul (by norm_num), one_div, ← Real.rpow_neg (by norm_num),
      ← Real.rpow_sub (by norm_num), Real.rpow_le_rpow_left_iff (by norm_num)]
    have : 2.9245 * (n : ℝ) ≤ 10 * L + 2.9245 := by
      have h := mul_le_mul_of_nonneg_left hfl2 (by norm_num : (0:ℝ) ≤ 2.9245)
      rw [mul_add, mul_div_cancel₀ _ (by norm_num)] at h
      linarith
    nlinarith
  have := lt_of_le_of_lt hlower key
  simpa using this
