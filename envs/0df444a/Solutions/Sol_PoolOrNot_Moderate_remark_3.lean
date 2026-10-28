-- Prove2me | solution 1 for PoolOrNot.Moderate.remark_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:05:20.792667+00:00
-- url     : https://prove2.me/submissions/9e2e3eaf-b99a-4f0d-a779-73bf50dffce4

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Chain

open PoolOrNot.Moderate in
theorem solution (μ θ ρ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (hρ1 : 1 < ρ) (hρ2 : ρ < 1 + θ / μ) :
    0 < qOf ρ μ θ ∧ qOf ρ μ θ < 1 ∧ ⌊qOf ρ μ θ⌋₊ = 0 ∧ qBar ρ μ θ = 1 ∧
    rOf ρ μ θ = qOf ρ μ θ ∧
    pMix ρ μ θ = rOf ρ μ θ * (μ + θ) / (ρ * μ) ∧
    rOf ρ μ θ * (μ + θ) / (ρ * μ) = 1 - (1 - rOf ρ μ θ) / ρ ∧
    rOf ρ μ θ * (μ + θ) / (ρ * μ) < 1 := by
  have hq : qOf ρ μ θ = μ * (ρ - 1) / θ := by
    unfold qOf; rw [max_eq_left (by linarith)]
  have hq0 : 0 < qOf ρ μ θ := by
    rw [hq]; exact div_pos (mul_pos hμ (by linarith)) hθ
  have hm : (ρ - 1) * μ < θ := (lt_div_iff₀ hμ).mp (by linarith)
  have hq1 : qOf ρ μ θ < 1 := by
    rw [hq, div_lt_one hθ]; linarith
  have hfl : ⌊qOf ρ μ θ⌋₊ = 0 := Nat.floor_eq_zero.mpr hq1
  have hqb : qBar ρ μ θ = 1 := by unfold qBar; rw [hfl]
  have hr : rOf ρ μ θ = qOf ρ μ θ := by unfold rOf; rw [hfl]; simp
  have hp : pMix ρ μ θ = rOf ρ μ θ * (μ + θ) / (ρ * μ) := by
    unfold pMix; rw [hqb]; norm_num
  have he : rOf ρ μ θ * (μ + θ) / (ρ * μ) = 1 - (1 - rOf ρ μ θ) / ρ := by
    rw [hr, hq]; field_simp; ring
  refine ⟨hq0, hq1, hfl, hqb, hr, hp, he, ?_⟩
  rw [he]
  have : 0 < (1 - rOf ρ μ θ) / ρ := div_pos (by rw [hr]; linarith) (by linarith)
  linarith
