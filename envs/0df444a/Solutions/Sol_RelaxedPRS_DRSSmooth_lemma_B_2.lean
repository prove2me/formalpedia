-- Prove2me | solution 1 for RelaxedPRS.DRSSmooth.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:13:40.335178+00:00
-- url     : https://prove2.me/submissions/b0b09f78-2117-46dd-8cc9-acf8cd866497

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open RelaxedPRS.DRSSmooth
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


theorem solution (β : ℝ) (hβ : 0 < β) (κ : ℝ)
    (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    IsLUB {r : ℝ | ∃ γ θ : ℝ, 0 < γ ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      θ * γ ^ 2 ≤ 2 * γ * β - γ ^ 3 / β ∧
      (1 - θ) * γ ^ 2 / β ^ 2 ≤ 1 ∧ r = γ / β} κ ∧
    (0 ≤ 1 - 1 / κ ^ 2 ∧ 1 - 1 / κ ^ 2 ≤ 1 ∧
      (1 - 1 / κ ^ 2) * (κ * β) ^ 2 = 2 * (κ * β) * β - (κ * β) ^ 3 / β ∧
      (1 - (1 - 1 / κ ^ 2)) * (κ * β) ^ 2 / β ^ 2 = 1) := by
  obtain ⟨hκ0, hp⟩ := hκ
  have hκ1 : 1 < κ := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos hκ0 (by linarith : (0:ℝ) < κ + 1)))]
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hβ2 : 0 < β ^ 2 := by positivity
  have mem2 : 0 ≤ 1 - 1 / κ ^ 2 ∧ 1 - 1 / κ ^ 2 ≤ 1 ∧
      (1 - 1 / κ ^ 2) * (κ * β) ^ 2 = 2 * (κ * β) * β - (κ * β) ^ 3 / β ∧
      (1 - (1 - 1 / κ ^ 2)) * (κ * β) ^ 2 / β ^ 2 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_one hκ2]; nlinarith
    · have : 0 ≤ 1 / κ ^ 2 := by positivity
      linarith
    · field_simp
      linear_combination hp
    · field_simp
      ring
  refine ⟨IsGreatest.isLUB ⟨⟨κ * β, 1 - 1 / κ ^ 2, by positivity, mem2.1, mem2.2.1,
      le_of_eq mem2.2.2.1, le_of_eq mem2.2.2.2, by field_simp⟩, ?_⟩, mem2⟩
  rintro r ⟨γ, θ, hγ, hθ0, hθ1, h1, h2, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = γ / β := ⟨_, rfl⟩
  rw [← hs]
  have hγs : γ = s * β := by rw [hs]; field_simp
  rw [hγs] at h1 h2
  have h1' : θ * s ^ 2 ≤ 2 * s - s ^ 3 := by
    have e : 2 * (s * β) * β - (s * β) ^ 3 / β = (2 * s - s ^ 3) * β ^ 2 := by
      field_simp
    rw [e] at h1
    have : θ * s ^ 2 * β ^ 2 ≤ (2 * s - s ^ 3) * β ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hβ2
  have h2' : (1 - θ) * s ^ 2 ≤ 1 := by
    have e : (1 - θ) * (s * β) ^ 2 / β ^ 2 = (1 - θ) * s ^ 2 := by field_simp
    rw [e] at h2; exact h2
  have hps : s ^ 3 + s ^ 2 - 2 * s - 1 ≤ 0 := by nlinarith
  by_contra hc
  push_neg at hc
  have hpos : 0 < s ^ 2 + s * κ + κ ^ 2 + s + κ - 2 := by nlinarith
  have : (s - κ) * (s ^ 2 + s * κ + κ ^ 2 + s + κ - 2) = (s ^ 3 + s ^ 2 - 2 * s - 1) - (κ ^ 3 + κ ^ 2 - 2 * κ - 1) := by ring
  nlinarith [mul_pos (sub_pos.mpr hc) hpos]
