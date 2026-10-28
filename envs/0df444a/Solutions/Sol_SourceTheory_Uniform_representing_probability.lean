-- Prove2me | solution 1 for SourceTheory.Uniform.representing_probability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:30:52.095363+00:00
-- url     : https://prove2.me/submissions/5f7c7fe4-44cc-4a00-9a0d-5e1a44039ecd

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model
import Theorems.Thm_SourceTheory_Uniform_lemma_B_1
import Theorems.Thm_SourceTheory_Uniform_qualitative_probability_representation

namespace STURPAux

open Set SourceTheory.Uniform MeasureTheory

lemma bet_act {S Γ : Type*} {𝓔 : Set (Set S)} (h : IsSetAlgebra 𝓔) {E : Set S} (hE : E ∈ 𝓔)
    (γ β : Γ) : IsActFrom 𝓔 (bet γ E β) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Set.toFinite ({γ, β} : Set Γ))
    rintro _ ⟨s, rfl⟩
    unfold bet
    split_ifs <;> simp
  · intro α
    by_cases h1 : γ = α <;> by_cases h2 : β = α
    · have : bet γ E β ⁻¹' {α} = univ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_univ, iff_true]
        split_ifs <;> simp_all
      rw [this]; exact h.univ_mem
    · have : bet γ E β ⁻¹' {α} = E := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff]
        split_ifs <;> simp_all
      rw [this]; exact hE
    · have : bet γ E β ⁻¹' {α} = Eᶜ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_compl_iff]
        split_ifs <;> simp_all
      rw [this]; exact h.compl_mem hE
    · have : bet γ E β ⁻¹' {α} = ∅ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        split_ifs <;> simp_all
      rw [this]; exact h.empty_mem

lemma W_le_of_null {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop}
    {U : Γ → ℝ} {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {X Y : Set S}
    (hX : X ∈ 𝓔) (hY : Y ∈ 𝓔) (hXY : X ⊆ Y) (hn : IsNull 𝓔 pref (Y \ X)) : W Y ≤ W X := by
  classical
  obtain ⟨α, β, -, hβα, -⟩ := h1.three_outcomes
  have hp := (hn (bet α X β) (bet α Y β) (bet_act h1.events hX α β) (bet_act h1.events hY α β)
    (by
      intro s hs
      simp only [mem_sdiff, not_and, not_not] at hs
      simp only [bet]
      by_cases h : s ∈ Y
      · simp [h, hs h]
      · have : s ∉ X := fun hx => h (hXY hx)
        simp [h, this])).1
  have := (h1.biseparable α β α β X hX Y hY hβα.le hβα.le).1 hp
  nlinarith

end STURPAux

open Set SourceTheory.Uniform MeasureTheory STURPAux

theorem solution {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (hpref : IsPreferredTo W 𝒮 𝒮)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔) (hreg : IsRegularRegion W 𝒮 B D)
    (hins : IsMoreInsensitive W 𝒮 𝒮 B D) :
    ∃ P : Set S → ℝ, IsProbOn 𝒮 P ∧ (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) ∧
      ∀ Q : Set S → ℝ, IsProbOn 𝒮 Q → (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) →
        ∀ E ∈ 𝒮, Q E = P E := by
  have hadd := lemma_B_1 𝓔 pref U W h1 𝒮 h𝒮 hpref B D hB hD hreg hins
  refine qualitative_probability_representation 𝒮 W h𝒮.algebra h1.W_empty h1.W_univ
    (fun A hA B hB hBA => h1.W_mono A (h𝒮.subset hA) B (h𝒮.subset hB) hBA) hadd
    h𝒮.convexRanged ?_
  rintro ⟨E, hE, hdisj, hpos, heq⟩
  apply h1.archimedean
  refine ⟨E, fun i => h𝒮.subset (hE i), hdisj, fun i hn => ?_, heq⟩
  have := W_le_of_null h1 h1.events.empty_mem (h𝒮.subset (hE i)) (empty_subset _)
    (by rwa [diff_empty])
  rw [h1.W_empty] at this
  linarith [hpos i]
