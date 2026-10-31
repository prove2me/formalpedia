-- Prove2me | solution 1 for TokenSignal.Asymmetry.alphaStar_range
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:04:27.446465+00:00
-- url     : https://prove2.me/submissions/51a799fa-17e0-42f4-9fe3-a477b4e6b2a1

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model
open TokenSignal.Asymmetry

theorem solution(P : Params) (hS : P.Standing) :
    0 < αStar P ∧ αStar P < 1 := by
  obtain ⟨hγ, hσ, hμ, hC, hI, hI2⟩ := hS
  have hs : 0 < P.σ ^ 2 * P.γ := by positivity
  have hd : 0 < 4 * P.μH - 4 * P.μL := by linarith
  have hsq0 : 0 ≤ (4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * P.σ ^ 2 * P.γ) := by positivity
  have hsq := Real.sq_sqrt hsq0
  have hr0 := Real.sqrt_nonneg ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * P.σ ^ 2 * P.γ))
  unfold αStar
  constructor
  · apply div_pos _ hs
    nlinarith [sq_nonneg (4 * P.μH - 4 * P.μL + P.σ ^ 2 * P.γ - Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * P.σ ^ 2 * P.γ)))]
  · rw [div_lt_one hs]
    nlinarith [mul_pos hd hs]
