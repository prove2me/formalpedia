-- Prove2me | solution 1 for UniformDRO.LowerBound.kl_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:57:04.131802+00:00
-- url     : https://prove2.me/submissions/d6edb0a4-03f0-421a-9c33-b0797decc139

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

open UniformDRO.LowerBound in
theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ ≤ pk k ρ) (hδq : δ ≤ (1 - pk k ρ) / 2) :
    BanditAlgorithm.bernoulliRelativeEntropy (pk k ρ - δ) (pk k ρ + δ) ≤
      8 * δ ^ 2 / (pk k ρ * (1 - pk k ρ)) := by
  obtain ⟨p, hp⟩ : ∃ p, p = pk k ρ := ⟨_, rfl⟩
  rw [← hp] at hδp hδq ⊢
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  set a := p - δ with ha
  set b := p + δ with hb
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have ha1 : 0 < 1 - a := by linarith
  have t1 : a * Real.log (a / b) ≤ a * (a / b - 1) := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hb0)) ha0
  have t2 : (1 - a) * Real.log ((1 - a) / (1 - b)) ≤ (1 - a) * ((1 - a) / (1 - b) - 1) :=
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha1 hb1)) ha1.le
  have hchi : a * (a / b - 1) + (1 - a) * ((1 - a) / (1 - b) - 1) = 4 * δ ^ 2 / (b * (1 - b)) := by
    have hbne : b ≠ 0 := hb0.ne'
    have hb1ne : 1 - b ≠ 0 := hb1.ne'
    have e : a * (a / b - 1) + (1 - a) * ((1 - a) / (1 - b) - 1) = (a - b) ^ 2 / (b * (1 - b)) := by
      field_simp
      ring
    have e2 : (a - b) ^ 2 = 4 * δ ^ 2 := by rw [ha, hb]; ring
    rw [e, e2]
  have hden : p * (1 - p) / 2 ≤ b * (1 - b) := by
    have h1 : p ≤ b := by linarith
    have h2 : (1 - p) / 2 ≤ 1 - b := by linarith
    nlinarith [mul_le_mul h1 h2 (by linarith) hb0.le]
  have hfin : 4 * δ ^ 2 / (b * (1 - b)) ≤ 8 * δ ^ 2 / (p * (1 - p)) := by
    rw [div_le_div_iff₀ (mul_pos hb0 hb1) (mul_pos hp0 (by linarith))]
    nlinarith [sq_nonneg δ]
  unfold BanditAlgorithm.bernoulliRelativeEntropy
  linarith
