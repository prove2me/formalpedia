-- Prove2me | solution 1 for RoboAdvising.Interaction.f_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:23.706166+00:00
-- url     : https://prove2.me/submissions/cac0a5ef-a9a2-4cb3-b2b8-4fd4f5d0402e

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

set_option autoImplicit false
open RoboAdvising.Interaction

theorem solution (P : Params) (hS : P.Standing) :
    (∀ φ : ℝ, 1 ≤ φ → 0 ≤ fAux P φ) ∧
    (P.pe = 0 → P.β = 0 → ∀ φ : ℝ, fAux P φ = 0) := by
  obtain ⟨h0, hse, hp0, hp1, hβ⟩ := hS
  constructor
  · intro φ hφ
    have hφ0 : 0 < φ := by linarith
    have hsq : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ0
    have ha0 : 0 ≤ P.β * P.sig0 := mul_nonneg hβ h0.le
    have ht0 : 0 ≤ (φ - 1) / 2 * P.pe := mul_nonneg (by linarith) hp0
    have hq : P.β * P.sig0 / Real.sqrt φ ≤ Real.sqrt (P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2) := by
      have e : P.β * P.sig0 / Real.sqrt φ = Real.sqrt ((P.β * P.sig0) ^ 2 / φ) := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq ha0]
      rw [e]
      apply Real.sqrt_le_sqrt
      rw [mul_pow]
      nlinarith [sq_nonneg P.se]
    have e : fAux P φ = P.β * P.sig0 / Real.sqrt φ
        + (φ - 1) / 2 * P.pe * (Real.sqrt (P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2)
          - P.β * P.sig0 / Real.sqrt φ) := by
      unfold fAux; ring
    rw [e]
    have : 0 ≤ P.β * P.sig0 / Real.sqrt φ := div_nonneg ha0 hsq.le
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hq)]
  · intro hp hb φ
    unfold fAux
    rw [hp, hb]; simp
