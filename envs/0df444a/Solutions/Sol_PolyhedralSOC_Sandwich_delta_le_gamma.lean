-- Prove2me | solution 1 for PolyhedralSOC.Sandwich.delta_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:01.708001+00:00
-- url     : https://prove2.me/submissions/0e0a7f55-905c-4245-86da-dc24167cfc57

import Mathlib

theorem solution (r ε R t δ : ℝ) (hr : 0 < r) (hε : 0 < ε) (ht : 0 ≤ t)
    (hγ : R * ε / r < 1) (hδ : δ = ε * t / (r + ε * t)) (hbound : (1 - δ) * t ≤ R) :
    t ≤ R / (1 - R * ε / r) ∧ δ ≤ R * ε / r := by
  have hden : 0 < r + ε * t := by
    have := mul_nonneg hε.le ht
    linarith
  have hRε : R * ε < r := by rwa [div_lt_one hr] at hγ
  have hone : 0 < 1 - R * ε / r := by linarith
  have hδval : 1 - δ = r / (r + ε * t) := by
    rw [hδ]; field_simp; try ring
  have hkey : t * (r - R * ε) ≤ R * r := by
    rw [hδval, div_mul_eq_mul_div, div_le_iff₀ hden] at hbound
    nlinarith [hbound]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hone]
    have hx : t * (1 - R * ε / r) = t * (r - R * ε) / r := by
      field_simp
      try ring
    rw [hx, div_le_iff₀ hr]
    nlinarith [hkey]
  · rw [hδ, div_le_div_iff₀ hden hr]
    nlinarith [hkey, mul_le_mul_of_nonneg_left hkey hε.le]
