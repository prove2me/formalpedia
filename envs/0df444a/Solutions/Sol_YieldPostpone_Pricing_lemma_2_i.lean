-- Prove2me | solution 1 for YieldPostpone.Pricing.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:21:43.395249+00:00
-- url     : https://prove2.me/submissions/bd5c184b-7267-46f2-9c11-92c84bf2096a

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting
open YieldPostpone.Pricing

theorem solution(P : Params) (hP : P.Valid) :
    0 ≤ cOR P ↔ P.α ≤ 1 / 2 ∧ P.θ ≤ (1 - 2 * P.α) / (2 * (1 - P.α)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hne : 1 - P.θ ≠ 0 := hθ'.ne'
  have hK : 0 < P.a / P.b * P.α * (1 - P.θ) :=
    mul_pos (mul_pos (div_pos ha hb) hα0) hθ'
  unfold cOR
  rw [mul_nonneg_iff_of_pos_left hK, sub_nonneg, Real.sqrt_le_iff]
  have e : P.α ^ 2 + P.θ / (1 - P.θ) ≤ (1 - P.α) ^ 2 ↔ P.θ ≤ (1 - 2 * P.α) * (1 - P.θ) := by
    rw [← sub_nonneg, show (1 - P.α) ^ 2 - (P.α ^ 2 + P.θ / (1 - P.θ))
        = ((1 - 2 * P.α) * (1 - P.θ) - P.θ) / (1 - P.θ) by field_simp; ring, div_nonneg_iff]
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · linarith
      · linarith
    · intro h
      left
      exact ⟨by linarith, hθ'.le⟩
  rw [e, le_div_iff₀ (show (0:ℝ) < 2 * (1 - P.α) by linarith)]
  constructor
  · rintro ⟨_, h⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by nlinarith⟩
