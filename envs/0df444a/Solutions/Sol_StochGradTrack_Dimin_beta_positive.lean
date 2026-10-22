-- Prove2me | solution 1 for StochGradTrack.Dimin.beta_positive
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:38:43.25167+00:00
-- url     : https://prove2.me/submissions/c628af84-20ae-4b92-93e9-d2c4f38ac396

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_StepSystem

set_option autoImplicit false
open StochGradTrack.Dimin

theorem solution (θ L m ρ : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hm : 0 < m) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (0 < (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2 ↔
      (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * Real.sqrt (1 + 3 * ρ ^ 2)) / (1 - ρ ^ 2) < m) ∧
    (0 < (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2 →
      ∀ k : ℕ, 0 < betaK θ m L ρ k) := by
  have hE : 0 < 1 - ρ ^ 2 := by nlinarith
  have hq2 : Real.sqrt (1 + 3 * ρ ^ 2) ^ 2 = 1 + 3 * ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hq0 : 0 ≤ Real.sqrt (1 + 3 * ρ ^ 2) := Real.sqrt_nonneg _
  generalize Real.sqrt (1 + 3 * ρ ^ 2) = q at hq2 hq0 ⊢
  have hqρ : 2 * ρ < q := by
    by_contra h
    push_neg at h
    nlinarith [mul_self_le_mul_self hq0 h]
  have hm2 : 0 < m ^ 2 := by positivity
  have key : (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2
      = ((1 - ρ ^ 2) * m ^ 2 - 8 * ρ ^ 2 * θ * L * m - 4 * ρ ^ 2 * θ ^ 2 * L ^ 2)
        / (2 * ρ ^ 2 * m ^ 2) := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [key, div_pos_iff_of_pos_right (by positivity), div_lt_iff₀ hE]
    have hfac : (1 - ρ ^ 2) * ((1 - ρ ^ 2) * m ^ 2 - 8 * ρ ^ 2 * θ * L * m - 4 * ρ ^ 2 * θ ^ 2 * L ^ 2)
        = ((1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * q)) *
          ((1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 - 2 * θ * L * ρ * q)) := by
      linear_combination (4 * ρ ^ 2 * θ ^ 2 * L ^ 2) * hq2
    have hpos : 0 < (1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 - 2 * θ * L * ρ * q) := by
      have : 0 < 2 * θ * L * ρ * (q - 2 * ρ) := by
        have := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hθ) hL) hρ0
        exact mul_pos this (by linarith)
      have h2 : 0 < (1 - ρ ^ 2) * m := mul_pos hE hm
      nlinarith
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      have h1 : (1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * q) ≤ 0 := by linarith
      have h2 : ((1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * q)) *
          ((1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 - 2 * θ * L * ρ * q)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1 hpos.le
      have h3 := mul_pos hE h
      rw [hfac] at h3
      linarith
    · intro h
      have h1 : 0 < (1 - ρ ^ 2) * m - (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * q) := by linarith
      have h3 := mul_pos h1 hpos
      rw [← hfac] at h3
      exact (mul_pos_iff_of_pos_left hE).1 h3
  · intro hβ k
    unfold betaK stepDimin
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmk : 0 < m + k := by linarith
    have hab : θ / (m + k) ≤ θ / m := div_le_div_of_nonneg_left hθ.le hm (by linarith)
    have ha0 : 0 ≤ θ / (m + k) := by positivity
    have e1 : 4 * θ * L / m = 4 * (θ / m) * L := by ring
    have e2 : 2 * θ ^ 2 * L ^ 2 / m ^ 2 = 2 * (θ / m) ^ 2 * L ^ 2 := by ring
    rw [e1, e2] at hβ
    have h1 : θ / (m + k) * L ≤ θ / m * L := mul_le_mul_of_nonneg_right hab hL.le
    have h2 : 0 ≤ θ / (m + k) * L := mul_nonneg ha0 hL.le
    have h3 : (θ / (m + k) * L) ^ 2 ≤ (θ / m * L) ^ 2 := by
      exact pow_le_pow_left₀ h2 h1 2
    have e3 : 2 * (θ / (m + k)) ^ 2 * L ^ 2 = 2 * (θ / (m + k) * L) ^ 2 := by ring
    have e4 : 2 * (θ / m) ^ 2 * L ^ 2 = 2 * (θ / m * L) ^ 2 := by ring
    rw [e4] at hβ
    rw [e3]
    nlinarith
