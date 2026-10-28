-- Prove2me | solution 1 for SourceTheory.Uniform.uniform_prob_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:30:52.853978+00:00
-- url     : https://prove2.me/submissions/d31337bc-a13a-40b9-8c69-31d75327b865

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model
import Theorems.Thm_SourceTheory_Uniform_source_function_exists
import Theorems.Thm_SourceTheory_Uniform_qualitative_probability_representation

namespace STUPUAux

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


lemma rep_of_uniform {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop}
    {U : Γ → ℝ} {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒮 : Set (Set S)}
    (h𝒮 : IsSource 𝓔 W 𝒮) {P : Set S → ℝ} (hP : IsUniformWith pref U 𝒮 P) :
    ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A := by
  obtain ⟨w, ⟨⟨-, hsm, -, -⟩, -⟩, hW⟩ := source_function_exists 𝓔 pref U W h1 𝒮 h𝒮 P hP
  obtain ⟨hP1, hP0, hPadd⟩ := hP.1
  have hrange : ∀ A ∈ 𝒮, P A ∈ Icc (0 : ℝ) 1 := by
    intro A hA
    have e := hPadd A hA Aᶜ (h𝒮.algebra.compl_mem hA) disjoint_compl_right
    rw [union_compl_self, hP1] at e
    exact ⟨hP0 A hA, by linarith [hP0 Aᶜ (h𝒮.algebra.compl_mem hA)]⟩
  intro A hA A' hA'
  rw [hW A hA, hW A' hA']
  exact hsm.le_iff_le (hrange A' hA') (hrange A hA)

end STUPUAux

open Set SourceTheory.Uniform MeasureTheory STUPUAux

theorem solution {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (P Q : Set S → ℝ) (hP : IsUniformWith pref U 𝒮 P) (hQ : IsUniformWith pref U 𝒮 Q) :
    ∀ E ∈ 𝒮, P E = Q E := by
  have hA := h𝒮.algebra
  have rP := rep_of_uniform h1 h𝒮 hP
  have rQ := rep_of_uniform h1 h𝒮 hQ
  obtain ⟨-, -, hPadd⟩ := hP.1
  have hadd : ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
      (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H)) := by
    intro E hE F hF H hH hEH hFH
    rw [rP E hE F hF, rP _ (hA.union_mem hE hH) _ (hA.union_mem hF hH),
      hPadd E hE H hH (Set.disjoint_iff_inter_eq_empty.2 hEH),
      hPadd F hF H hH (Set.disjoint_iff_inter_eq_empty.2 hFH)]
    constructor <;> intro h <;> linarith
  obtain ⟨R, -, -, huniq⟩ := qualitative_probability_representation 𝒮 W hA h1.W_empty h1.W_univ
    (fun A hA B hB hBA => h1.W_mono A (h𝒮.subset hA) B (h𝒮.subset hB) hBA) hadd
    h𝒮.convexRanged (by
      rintro ⟨E, hE, hdisj, hpos, heq⟩
      apply h1.archimedean
      refine ⟨E, fun i => h𝒮.subset (hE i), hdisj, fun i hn => ?_, heq⟩
      have := W_le_of_null h1 h1.events.empty_mem (h𝒮.subset (hE i)) (empty_subset _)
        (by rwa [sdiff_empty])
      rw [h1.W_empty] at this
      linarith [hpos i])
  intro E hE
  rw [huniq P hP.1 rP E hE, huniq Q hQ.1 rQ E hE]
