-- Prove2me | solution 1 for SupplyDemand.ibn_taymiyyah
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:22:12.00329+00:00
-- url     : https://prove2.me/submissions/fc0480ee-43f1-45ae-8a2d-02a57332769f

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (I : Set ℝ) (S₁ S₂ D₁ D₂ : ℝ → ℝ)
    (hS₁ : StrictMonoOn S₁ I) (hS₂ : StrictMonoOn S₂ I)
    (hD₁ : StrictAntiOn D₁ I) (hD₂ : StrictAntiOn D₂ I)
    {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ∈ I) (hp₂ : p₂ ∈ I)
    (h₁ : IsEquilibrium S₁ D₁ p₁ q₁) (h₂ : IsEquilibrium S₂ D₂ p₂ q₂) :
    ((∀ p ∈ I, D₁ p < D₂ p) → (∀ p ∈ I, S₂ p < S₁ p) → p₁ < p₂) ∧
    ((∀ p ∈ I, D₂ p < D₁ p) → (∀ p ∈ I, S₁ p < S₂ p) → p₂ < p₁) := by
  rcases h₁ with ⟨hd₁, hs₁⟩
  rcases h₂ with ⟨hd₂, hs₂⟩
  constructor
  · intro hDshift hSshift
    rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
    · exact hlt
    · subst p₂
      have hda : D₁ p₁ < D₂ p₁ := hDshift p₁ hp₁
      have hsa : S₂ p₁ < S₁ p₁ := hSshift p₁ hp₁
      rw [hd₁, hd₂] at hda
      rw [hs₂, hs₁] at hsa
      linarith
    · have hda : D₁ p₁ < D₂ p₁ := hDshift p₁ hp₁
      have hdb : D₂ p₁ < D₂ p₂ := hD₂ hp₂ hp₁ hgt
      have hsa : S₂ p₂ < S₁ p₂ := hSshift p₂ hp₂
      have hsb : S₁ p₂ < S₁ p₁ := hS₁ hp₂ hp₁ hgt
      rw [hd₁] at hda
      rw [hd₂] at hdb
      rw [hs₂] at hsa
      rw [hs₁] at hsb
      linarith
  · intro hDshift hSshift
    rcases lt_trichotomy p₂ p₁ with hlt | heq | hgt
    · exact hlt
    · subst p₂
      have hda : D₂ p₁ < D₁ p₁ := hDshift p₁ hp₁
      have hsa : S₁ p₁ < S₂ p₁ := hSshift p₁ hp₁
      rw [hd₂, hd₁] at hda
      rw [hs₁, hs₂] at hsa
      linarith
    · have hda : D₂ p₂ < D₁ p₂ := hDshift p₂ hp₂
      have hdb : D₁ p₂ < D₁ p₁ := hD₁ hp₁ hp₂ hgt
      have hsa : S₁ p₁ < S₂ p₁ := hSshift p₁ hp₁
      have hsb : S₂ p₁ < S₂ p₂ := hS₂ hp₁ hp₂ hgt
      rw [hd₂] at hda
      rw [hd₁] at hdb
      rw [hs₁] at hsa
      rw [hs₂] at hsb
      linarith
