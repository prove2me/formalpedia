-- Prove2me | solution 1 for QuantumWalkSearch.PhaseReflection.single_copy_bound
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:05:18.362863+00:00
-- url     : https://prove2.me/submissions/f775780a-8323-4c7e-98d7-d5464a8f6b83

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit

open QuantumWalkSearch.PhaseReflection

theorem solution (Δ θ : ℝ) (hΔ : 0 < Δ) (hΔπ : Δ ≤ Real.pi) (hθ₁ : Δ / 2 ≤ θ)
    (hθ₂ : θ ≤ Real.pi - Δ / 2) :
    |Real.sin (2 ^ precision Δ * θ)| / (2 ^ precision Δ * Real.sin θ) ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  have hsinΔ : Δ / Real.pi ≤ Real.sin (Δ / 2) := by
    have h := Real.mul_le_sin (x := Δ / 2) (by linarith) (by linarith)
    calc Δ / Real.pi = 2 / Real.pi * (Δ / 2) := by field_simp
      _ ≤ Real.sin (Δ / 2) := h
  have hsinθ : Real.sin (Δ / 2) ≤ Real.sin θ := by
    rcases le_or_gt θ (Real.pi / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hθ₁
    · rw [← Real.sin_pi_sub θ]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hpow : 2 * Real.pi / Δ ≤ (2 : ℝ) ^ precision Δ := by
    unfold precision
    have hx : 0 < 2 * Real.pi / Δ := by positivity
    have h1 : Real.logb 2 (2 * Real.pi / Δ) ≤ (⌈Real.logb 2 (2 * Real.pi / Δ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp h1
    rw [Real.rpow_natCast] at h2
    exact h2
  have hsinpos : 0 < Real.sin θ := by
    have : 0 < Δ / Real.pi := by positivity
    linarith
  have hpos : 0 < (2 : ℝ) ^ precision Δ * Real.sin θ := by positivity
  rw [div_le_iff₀ hpos]
  have hprod : 2 ≤ (2 : ℝ) ^ precision Δ * Real.sin θ := by
    calc (2 : ℝ) = 2 * Real.pi / Δ * (Δ / Real.pi) := by field_simp
      _ ≤ (2 : ℝ) ^ precision Δ * Real.sin θ :=
          mul_le_mul hpow (le_trans hsinΔ hsinθ) (by positivity) (by positivity)
  calc |Real.sin (2 ^ precision Δ * θ)| ≤ 1 := Real.abs_sin_le_one _
    _ = 1 / 2 * 2 := by norm_num
    _ ≤ 1 / 2 * ((2 : ℝ) ^ precision Δ * Real.sin θ) := by gcongr
