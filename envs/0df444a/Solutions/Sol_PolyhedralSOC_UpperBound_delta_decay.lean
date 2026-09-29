-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.delta_decay
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:24:54.519863+00:00
-- url     : https://prove2.me/submissions/a78ca07a-2f8e-4182-9432-dccda302101d

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

open PolyhedralSOC.UpperBound

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℕ, 1 ≤ ν → delta ν ≤ C / 4 ^ ν := by
  refine ⟨4, by norm_num, ?_⟩
  intro ν hν
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi34 : Real.pi ≤ 4 := Real.pi_le_four
  have hpow : (0:ℝ) < 2 ^ (ν + 1) := by positivity
  have h4 : (4:ℝ) ≤ 2 ^ (ν + 1) := by
    have h2 : (2:ℝ) ^ 2 ≤ 2 ^ (ν + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    norm_num at h2
    exact h2
  have hθpos : 0 < Real.pi / 2 ^ (ν + 1) := by positivity
  have hθle : Real.pi / 2 ^ (ν + 1) ≤ Real.pi / 4 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) h4
  -- cos θ ≥ cos (π/3) = 1/2
  have hπ3 : Real.pi / 4 ≤ Real.pi / 3 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) (by norm_num)
  have hcosge : (1:ℝ) / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hθpos.le
      (by linarith : Real.pi / 3 ≤ Real.pi) (le_trans hθle hπ3)
    rwa [Real.cos_pi_div_three] at hmono
  have hcospos : 0 < Real.cos (Real.pi / 2 ^ (ν + 1)) := by linarith
  -- 1 - cos θ ≤ θ²/2
  have hlow : 1 - (Real.pi / 2 ^ (ν + 1)) ^ 2 / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) :=
    Real.one_sub_sq_div_two_le_cos
  -- δ ν = (1 - cos θ)/cos θ ≤ 2 (1 - cos θ) ≤ θ²
  have hdelta : delta ν ≤ (Real.pi / 2 ^ (ν + 1)) ^ 2 := by
    have hd : delta ν = (1 - Real.cos (Real.pi / 2 ^ (ν + 1))) /
        Real.cos (Real.pi / 2 ^ (ν + 1)) := by
      rw [delta]
      field_simp
    rw [hd, div_le_iff₀ hcospos]
    nlinarith [hlow, hcosge, sq_nonneg (Real.pi / 2 ^ (ν + 1))]
  -- θ² = π²/4^{ν+1} ≤ 3/4^ν
  have hsq : (Real.pi / 2 ^ (ν + 1)) ^ 2 = Real.pi ^ 2 / 4 ^ (ν + 1) := by
    rw [div_pow]
    congr 1
    rw [← pow_mul]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  obtain ⟨q, hq, hqpos⟩ : ∃ q : ℝ, q = (4:ℝ) ^ ν ∧ 0 < q := ⟨4 ^ ν, rfl, by positivity⟩
  have h41 : (4:ℝ) ^ (ν + 1) = 4 * q := by rw [hq, pow_succ]; ring
  have hp16 : Real.pi ^ 2 ≤ 16 := by nlinarith [hpi, hpi34]
  rw [hsq, h41] at hdelta
  have hstep : Real.pi ^ 2 / (4 * q) ≤ 4 / q := by
    rw [div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [mul_le_mul_of_nonneg_right hp16 hqpos.le]
  have hgoal : delta ν ≤ 4 / q := le_trans hdelta hstep
  rw [hq] at hgoal
  exact hgoal
