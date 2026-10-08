-- Prove2me | solution 1 for RhinViola.existsExponentSlack
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T10:14:28.072645+00:00
-- url     : https://prove2.me/submissions/8251027d-ace4-4fb2-9034-6305f2409e9f

import Mathlib.Tactic

theorem solution
    (σ ρ ε : ℝ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < σ ∧
      (σ + ρ + 2 * δ) / (σ - δ) < 1 + ρ / σ + ε := by
  let K : ℝ := 3 * σ + ρ + ε * σ
  have hK : 0 < K := by
    dsimp [K]
    have heσ : 0 < ε * σ := mul_pos hε hσ
    nlinarith
  let δ : ℝ := ε * σ ^ 2 / (2 * K)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδσ : δ < σ := by
    have h2K : 0 < 2 * K := by positivity
    have hcompare : ε * σ < 2 * K := by
      dsimp [K]
      have heσ : 0 < ε * σ := mul_pos hε hσ
      nlinarith
    have hscaled := mul_lt_mul_of_pos_left hcompare hσ
    dsimp [δ]
    apply (div_lt_iff₀ h2K).2
    nlinarith
  refine ⟨δ, hδ, hδσ, ?_⟩
  have hden : 0 < σ - δ := sub_pos.mpr hδσ
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have htarget :
      1 + ρ / σ + ε = (σ + ρ + ε * σ) / σ := by
    field_simp [hσne]
  have hpoly :
      (σ + ρ + ε * σ) * (σ - δ) -
          (σ + ρ + 2 * δ) * σ = ε * σ ^ 2 / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hK]
    ring
  rw [div_lt_iff₀ hden, htarget, div_mul_eq_mul_div]
  apply (lt_div_iff₀ hσ).2
  have hpos : 0 < ε * σ ^ 2 / 2 := by positivity
  nlinarith
