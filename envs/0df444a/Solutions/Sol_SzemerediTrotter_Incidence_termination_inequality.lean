-- Prove2me | solution 1 for SzemerediTrotter.Incidence.termination_inequality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:56:32.20042+00:00
-- url     : https://prove2.me/submissions/5a151ae5-188b-4293-be5b-17b9d5969a3f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution :
    ∀ i : ℕ, 30 ≤ i →
      (200 : ℝ) / ((0.1 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ))
        ≤ (2 : ℝ) ^ ((i : ℝ) / 3) * (1 - 2 / (10 : ℝ) ^ 10) ^ (4 * (i : ℝ) / 3) := by
  intro i hi
  let B : ℝ := 1 - 2 / (10 : ℝ) ^ 10
  have hB : 0 ≤ B := by norm_num [B]
  have hroot : (2 / 5 : ℝ) ≤ (0.1 : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      (2 / 5 : ℝ) = ((2 / 5 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 / 5 : ℝ))]
        norm_num
      _ ≤ (0.1 : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
  have htwo : 1 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hden : (2 / 5 : ℝ) ≤ (0.1 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) :=
    hroot.trans (le_mul_of_one_le_right (by positivity) htwo)
  have hlhs : (200 : ℝ) / ((0.1 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ)) ≤ 500 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hexp : (10 : ℝ) ≤ (i : ℝ) / 3 := by
    have : (30 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  have hbase : (19 / 10 : ℝ) ≤ 2 * B ^ 4 := by norm_num [B]
  have hR : (500 : ℝ) ≤ (2 * B ^ 4) ^ ((i : ℝ) / 3) := by
    calc
      (500 : ℝ) ≤ (19 / 10 : ℝ) ^ (10 : ℝ) := by norm_num
      _ ≤ (19 / 10 : ℝ) ^ ((i : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ (2 * B ^ 4) ^ ((i : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) hbase (by positivity)
  apply hlhs.trans
  calc
    (500 : ℝ) ≤ (2 * B ^ 4) ^ ((i : ℝ) / 3) := hR
    _ = (2 : ℝ) ^ ((i : ℝ) / 3) * B ^ (4 * (i : ℝ) / 3) := by
      rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by positivity)]
      rw [show 4 * (i : ℝ) / 3 = (4 : ℝ) * ((i : ℝ) / 3) by ring,
        Real.rpow_mul hB]
      norm_num
