-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_numerical
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:26:59.842996+00:00
-- url     : https://prove2.me/submissions/6bcb5e42-6c1c-4d9e-a8f2-8c670fd7df96

import Mathlib
set_option autoImplicit false

theorem solution (s : ℝ) (hs : s ∈ Set.Icc (0.74 : ℝ) 0.75) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (0.8 : ℝ) ≤ (1 / (p * s) - 1 / Real.exp 1) *
      Real.log ((1 / (p * s) + p / Real.exp 1) / (1 / (p * s) + p / Real.exp 1 - 1)) := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hp0, hp1⟩ := hp
  norm_num at hs1 hs2
  have hec : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hpc : p / Real.exp 1 = p * (1 / Real.exp 1) := by ring
  rw [hpc]
  generalize hcdef : 1 / Real.exp 1 = c
  have hc0 : 0 < c := by rw [← hcdef]; positivity
  have hc1 : c < 1 / 2.7 := by
    rw [← hcdef]; exact one_div_lt_one_div_of_lt (by norm_num) hec
  have hps : 0 < p * s := by positivity
  generalize hudef : 1 / (p * s) = u
  have hu1 : 4 / 3 ≤ u := by
    rw [← hudef]
    have h1 : p * s ≤ 0.75 := by nlinarith
    have := one_div_le_one_div_of_le hps h1
    norm_num at this ⊢
    linarith
  have hpc1 : p * c ≤ c := by nlinarith
  have hpc0 : 0 < p * c := by positivity
  have hy : 0 < u + p * c - 1 := by linarith
  have hxy : (u + p * c) / (u + p * c - 1) = 1 + (u + p * c - 1)⁻¹ := by
    field_simp
    ring
  rw [hxy]
  have hser := Real.hasSum_log_one_add_inv hy
  have hlow : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * (u + p * c - 1) + 1)) ^ (2 * 0 + 1)
      ≤ Real.log (1 + (u + p * c - 1)⁻¹) := by
    apply le_hasSum hser 0
    intro j _
    have : 0 < 2 * (u + p * c - 1) + 1 := by linarith
    positivity
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one] at hlow
  have hd : 0 < 2 * (u + p * c - 1) + 1 := by linarith
  have hfin : 0.8 ≤ (u - c) * (2 * (1 / (2 * (u + p * c - 1) + 1))) := by
    have : (u - c) * (2 * (1 / (2 * (u + p * c - 1) + 1))) = 2 * (u - c) / (2 * (u + p * c - 1) + 1) := by
      field_simp
    rw [this, le_div_iff₀ hd]
    have h27 : 3.6 * c < 4 / 3 := by
      have := mul_lt_mul_of_pos_left hc1 (by norm_num : (0:ℝ) < 3.6)
      norm_num at this ⊢
      linarith
    nlinarith
  have hu0 : 0 ≤ u - c := by linarith [show c < 1 by linarith [(by norm_num : (1:ℝ)/2.7 < 1)]]
  calc (0.8 : ℝ) ≤ (u - c) * (2 * (1 / (2 * (u + p * c - 1) + 1))) := hfin
    _ ≤ (u - c) * Real.log (1 + (u + p * c - 1)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hu0
        simpa using hlow
