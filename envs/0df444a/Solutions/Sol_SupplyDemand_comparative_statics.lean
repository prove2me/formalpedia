-- Prove2me | solution 1 for SupplyDemand.comparative_statics
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:23:45.027933+00:00
-- url     : https://prove2.me/submissions/0f0549b0-e43f-4894-bd45-43cc942a52f5

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (I : Set ℝ) :
    (∀ (S D₁ D₂ : ℝ → ℝ), StrictMonoOn S I → StrictAntiOn D₁ I → StrictAntiOn D₂ I →
      (∀ p ∈ I, D₁ p < D₂ p) →
      ∀ p₁ q₁ p₂ q₂ : ℝ, p₁ ∈ I → p₂ ∈ I →
        IsEquilibrium S D₁ p₁ q₁ → IsEquilibrium S D₂ p₂ q₂ →
        p₁ < p₂ ∧ q₁ < q₂) ∧
    (∀ (S₁ S₂ D : ℝ → ℝ), StrictMonoOn S₁ I → StrictMonoOn S₂ I → StrictAntiOn D I →
      (∀ p ∈ I, S₁ p < S₂ p) →
      ∀ p₁ q₁ p₂ q₂ : ℝ, p₁ ∈ I → p₂ ∈ I →
        IsEquilibrium S₁ D p₁ q₁ → IsEquilibrium S₂ D p₂ q₂ →
        p₂ < p₁ ∧ q₁ < q₂) := by
  constructor
  · intro S D₁ D₂ hS hD₁ hD₂ hshift p₁ q₁ p₂ q₂ hp₁ hp₂ h₁ h₂
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
  · intro S₁ S₂ D hS₁ hS₂ hD hshift p₁ q₁ p₂ q₂ hp₁ hp₂ h₁ h₂
    rcases h₁ with ⟨hd₁, hs₁⟩
    rcases h₂ with ⟨hd₂, hs₂⟩
    have hp : p₂ < p₁ := by
      rcases lt_trichotomy p₂ p₁ with hlt | heq | hgt
      · exact hlt
      · have hsh : S₁ p₁ < S₂ p₁ := hshift p₁ hp₁
        have heqD : D p₂ = D p₁ := congrArg D heq
        have hS₂at : S₂ p₁ = q₂ := by simpa only [heq] using hs₂
        rw [hs₁, hS₂at] at hsh
        rw [hd₁, hd₂] at heqD
        linarith
      · have hDr : D p₂ < D p₁ := hD hp₁ hp₂ hgt
        have hSr : S₂ p₁ < S₂ p₂ := hS₂ hp₁ hp₂ hgt
        have hsh : S₁ p₁ < S₂ p₁ := hshift p₁ hp₁
        rw [hd₁, hd₂] at hDr
        rw [hs₂] at hSr
        rw [hs₁] at hsh
        linarith
    constructor
    · exact hp
    · have hQ : D p₁ < D p₂ := hD hp₂ hp₁ hp
      simpa only [hd₁, hd₂] using hQ
