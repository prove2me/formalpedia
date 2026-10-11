-- Prove2me | solution 1 for SupplyDemand.equilibrium_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:18:52.863371+00:00
-- url     : https://prove2.me/submissions/0d7afecb-a494-4fe3-bbd2-4ec1b211e78f

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (I : Set ℝ) (S D : ℝ → ℝ)
    (hS : StrictMonoOn S I) (hD : StrictAntiOn D I)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S D p₁ q₁) (h₂ : IsEquilibrium S D p₂ q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  rcases h₁ with ⟨hd₁, hs₁⟩
  rcases h₂ with ⟨hd₂, hs₂⟩
  have hp : p₁ = p₂ := by
    rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
    · have hs : S p₁ < S p₂ := hS hp₁ hp₂ hlt
      have hd : D p₂ < D p₁ := hD hp₁ hp₂ hlt
      rw [hs₁, hs₂] at hs
      rw [hd₁, hd₂] at hd
      exact (lt_irrefl q₁ (lt_trans hs hd)).elim
    · exact heq
    · have hs : S p₂ < S p₁ := hS hp₂ hp₁ hgt
      have hd : D p₁ < D p₂ := hD hp₂ hp₁ hgt
      rw [hs₁, hs₂] at hs
      rw [hd₁, hd₂] at hd
      exact (lt_irrefl q₂ (lt_trans hs hd)).elim
  constructor
  · exact hp
  · calc
      q₁ = S p₁ := hs₁.symm
      _ = S p₂ := by rw [hp]
      _ = q₂ := hs₂
