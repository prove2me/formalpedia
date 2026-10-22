-- Prove2me | solution 1 for StochGradTrack.Const.beta_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:25:57.024129+00:00
-- url     : https://prove2.me/submissions/e116a763-91d5-4bec-98de-ecb720eb6f92

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model
import Definitions.Def_StochGradTrack_Const_Matrix

set_option autoImplicit false
open StochGradTrack.Const

theorem solution (α L ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hL : 0 < L) (hα : 0 < α)
    (h7a : α ≤ (1 - ρ ^ 2) / (12 * ρ * L)) :
    (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2)
        ≤ betaT α L ρ ∧
      11 * (1 - ρ ^ 2) / (72 * ρ ^ 2) ≤
        (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2) ∧
      (1 - ρ ^ 2) / (8 * ρ ^ 2) ≤ betaT α L ρ ∧ 0 < betaT α L ρ := by
  have hs : 0 < 1 - ρ ^ 2 := by nlinarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hLne : L ≠ 0 := hL.ne'
  have hu : α * L ≤ (1 - ρ ^ 2) / (12 * ρ) := by
    have h := mul_le_mul_of_nonneg_right h7a hL.le
    have : (1 - ρ ^ 2) / (12 * ρ * L) * L = (1 - ρ ^ 2) / (12 * ρ) := by field_simp
    linarith
  have hu0 : 0 < α * L := mul_pos hα hL
  have hA : 4 * (α * L) ≤ (1 - ρ ^ 2) / (3 * ρ) := by
    have : 4 * ((1 - ρ ^ 2) / (12 * ρ)) = (1 - ρ ^ 2) / (3 * ρ) := by field_simp; ring
    linarith
  have hB : 2 * (α * L) ^ 2 ≤ (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2) := by
    have h1 : (α * L) ^ 2 ≤ ((1 - ρ ^ 2) / (12 * ρ)) ^ 2 := pow_le_pow_left₀ hu0.le hu 2
    have : 2 * ((1 - ρ ^ 2) / (12 * ρ)) ^ 2 = (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2) := by
      field_simp; ring
    linarith
  have hβ : betaT α L ρ = (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * (α * L) - 2 * (α * L) ^ 2 := by
    unfold betaT; ring
  have h1 : (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2)
      ≤ betaT α L ρ := by
    rw [hβ]; linarith
  have h2 : 11 * (1 - ρ ^ 2) / (72 * ρ ^ 2) ≤
      (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2) := by
    rw [← sub_nonneg]
    have : (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2)
        - 11 * (1 - ρ ^ 2) / (72 * ρ ^ 2)
        = (1 - ρ ^ 2) * (ρ ^ 2 - 24 * ρ + 24) / (72 * ρ ^ 2) := by
      field_simp; ring
    rw [this]
    apply div_nonneg
    · apply mul_nonneg hs.le; nlinarith
    · positivity
  have h3 : (1 - ρ ^ 2) / (8 * ρ ^ 2) ≤ 11 * (1 - ρ ^ 2) / (72 * ρ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hs hρ2]
  have h4 : (1 - ρ ^ 2) / (8 * ρ ^ 2) ≤ betaT α L ρ := by linarith
  exact ⟨h1, h2, h4, lt_of_lt_of_le (div_pos hs (by positivity)) h4⟩
