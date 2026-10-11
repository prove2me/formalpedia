-- Prove2me | solution 1 for SupplyDemand.supply_increase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:21:01.163561+00:00
-- url     : https://prove2.me/submissions/0ea748a3-ad40-462d-98c3-622bc0d4530d

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (I : Set ℝ) (S₁ S₂ D : ℝ → ℝ)
    (hS₁ : StrictMonoOn S₁ I) (hS₂ : StrictMonoOn S₂ I) (hD : StrictAntiOn D I)
    (hshift : ∀ p ∈ I, S₁ p < S₂ p)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S₁ D p₁ q₁) (h₂ : IsEquilibrium S₂ D p₂ q₂) :
    p₂ < p₁ ∧ q₁ < q₂ := by
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
