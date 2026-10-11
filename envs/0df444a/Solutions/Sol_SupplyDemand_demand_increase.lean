-- Prove2me | solution 1 for SupplyDemand.demand_increase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:20:46.62711+00:00
-- url     : https://prove2.me/submissions/947d9367-0e29-4335-9744-c59397f61503

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (I : Set ℝ) (S D₁ D₂ : ℝ → ℝ)
    (hS : StrictMonoOn S I) (hD₁ : StrictAntiOn D₁ I) (hD₂ : StrictAntiOn D₂ I)
    (hshift : ∀ p ∈ I, D₁ p < D₂ p)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S D₁ p₁ q₁) (h₂ : IsEquilibrium S D₂ p₂ q₂) :
    p₁ < p₂ ∧ q₁ < q₂ := by
  rcases h₁ with ⟨hd₁, hs₁⟩
  rcases h₂ with ⟨hd₂, hs₂⟩
  have hp : p₁ < p₂ := by
    rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
    · exact hlt
    · have hsh : D₁ p₁ < D₂ p₁ := hshift p₁ hp₁
      have heqS : S p₁ = S p₂ := congrArg S heq
      rw [hd₁, heq, hd₂] at hsh
      rw [hs₁, hs₂] at heqS
      linarith
    · have hSr : S p₂ < S p₁ := hS hp₂ hp₁ hgt
      have hDr : D₂ p₁ < D₂ p₂ := hD₂ hp₂ hp₁ hgt
      have hsh : D₁ p₁ < D₂ p₁ := hshift p₁ hp₁
      rw [hs₁, hs₂] at hSr
      rw [hd₁] at hsh
      rw [hd₂] at hDr
      linarith
  constructor
  · exact hp
  · have hQ : S p₁ < S p₂ := hS hp₁ hp₂ hp
    simpa only [hs₁, hs₂] using hQ
