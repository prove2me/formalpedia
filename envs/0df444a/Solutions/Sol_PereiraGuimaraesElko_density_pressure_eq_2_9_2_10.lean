-- Prove2me | solution 1 for PereiraGuimaraesElko.density_pressure_eq_2_9_2_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:15:15.44201+00:00
-- url     : https://prove2.me/submissions/e9bda460-1730-4b68-a3df-263dc08c93e7

import Mathlib

theorem solution (κ H Hdot Φ Φdot V ρ p : ℝ)
    (h29 : ρ = Φdot ^ 2 / 2 + V + 3 / 8 * (H ^ 2 * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8))
    (h210 : p = Φdot ^ 2 / 2 - V - 3 / 8 * (H ^ 2 * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8)
        - 1 / 4 * (Hdot * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8)
        - 1 / 2 * (H * Φ * Φdot) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2) :
    (H ^ 2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φ ^ 2 / 8) * (Φdot ^ 2 / 2 + V) ↔
        H ^ 2 = κ ^ 2 / 3 * ρ) ∧
      (Hdot = -(κ ^ 2 / 2) * (1 + κ ^ 2 * Φ ^ 2 / 8) *
          (Φdot ^ 2 - 1 / 2 * (H * Φ * Φdot) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2) ↔
        Hdot = -(κ ^ 2 / 2) * (ρ + p)) := by
  set D := 1 + κ ^ 2 * Φ ^ 2 / 8 with hD
  have hD0 : 0 < D := by positivity
  have e : κ ^ 2 * Φ ^ 2 = 8 * (D - 1) := by rw [hD]; ring
  have k1 : (H ^ 2 - κ ^ 2 / 3 * ρ) * D = H ^ 2 - κ ^ 2 / 3 * D * (Φdot ^ 2 / 2 + V) := by
    rw [h29]; field_simp; linear_combination (-(1/8) * H ^ 2) * e
  have k2 : (Hdot - -(κ ^ 2 / 2) * (ρ + p)) * D = Hdot - -(κ ^ 2 / 2) * D *
          (Φdot ^ 2 - 1 / 2 * (H * Φ * Φdot) / D ^ 2) := by
    rw [h29, h210]; field_simp; linear_combination (-(1/8) * Hdot * D) * e
  constructor
  · constructor
    · intro h1
      have : (H ^ 2 - κ ^ 2 / 3 * ρ) * D = 0 := by rw [k1]; linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · linarith
      · exact absurd h2 hD0.ne'
    · intro h1
      have : H ^ 2 - κ ^ 2 / 3 * D * (Φdot ^ 2 / 2 + V) = 0 := by rw [← k1, h1]; ring
      linarith
  · constructor
    · intro h1
      have : (Hdot - -(κ ^ 2 / 2) * (ρ + p)) * D = 0 := by rw [k2]; linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · linarith
      · exact absurd h2 hD0.ne'
    · intro h1
      have : Hdot - -(κ ^ 2 / 2) * D * (Φdot ^ 2 - 1 / 2 * (H * Φ * Φdot) / D ^ 2) = 0 := by
        rw [← k2, h1]; ring
      linarith
