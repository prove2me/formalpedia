-- Prove2me | solution 1 for SourceTheory.Uniform.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:38.436623+00:00
-- url     : https://prove2.me/submissions/abac690b-4594-481a-a6a4-2e3f15ac2c35

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set SourceTheory.Uniform

namespace MMC

lemma part3_of {S : Type*} {𝒮 : Set (Set S)} (h : MeasureTheory.IsSetAlgebra 𝒮) {S1 T : Set S}
    (h1 : S1 ∈ 𝒮) (hT : T ∈ 𝒮) (hsub : S1 ⊆ T) : IsPartition3 𝒮 S1 (T \ S1) Tᶜ := by
  refine ⟨h1, h.sdiff_mem hT h1, h.compl_mem hT, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx' (hsub hx)
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx'  hx.1
  · ext x; simp only [mem_union, mem_diff, mem_compl_iff, mem_univ, iff_true]; tauto

lemma part3_sub {S : Type*} {𝒮 : Set (Set S)} {C1 C2 C3 : Set S} (hp : IsPartition3 𝒮 C1 C2 C3) :
    C1 ⊆ C3ᶜ := by
  intro x hx hx3
  exact (Set.disjoint_left.mp hp.2.2.2.2.1) hx hx3

lemma part3_sub2 {S : Type*} {𝒮 : Set (Set S)} {C1 C2 C3 : Set S} (hp : IsPartition3 𝒮 C1 C2 C3) :
    C2 ⊆ C3ᶜ := by
  intro x hx hx3
  exact (Set.disjoint_left.mp hp.2.2.2.2.2.1) hx hx3

lemma part3_disj12 {S : Type*} {𝒮 : Set (Set S)} {C1 C2 C3 : Set S} (hp : IsPartition3 𝒮 C1 C2 C3) :
    Disjoint C1 C2 := hp.2.2.2.1

lemma mono_ev {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop} {U : Γ → ℝ}
    {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒮 : Set (Set S)} (h𝒮 : IsSource 𝓔 W 𝒮)
    {A C : Set S} (hA : A ∈ 𝒮) (hC : C ∈ 𝒮) (hAC : A ⊆ C) : W A ≤ W C :=
  h1.W_mono C (h𝒮.subset hC) A (h𝒮.subset hA) hAC

lemma refine_part {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop} {U : Γ → ℝ}
    {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒞 : Set (Set S)} (h𝒞 : IsSource 𝓔 W 𝒞)
    {C1 C2 C3 : Set S} (hC : IsPartition3 𝒞 C1 C2 C3) (μ ν : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ W C1)
    (hν : W (C3ᶜ) ≤ ν) (hν1 : ν ≤ 1) :
    ∃ C1' C2' C3' : Set S, IsPartition3 𝒞 C1' C2' C3' ∧ W C1' = μ ∧ W (C3'ᶜ) = ν ∧ C2 ⊆ C2' := by
  have hCe : ∅ ∈ 𝒞 := h𝒞.algebra.empty_mem
  have hCu : (univ : Set S) ∈ 𝒞 := h𝒞.algebra.univ_mem
  have hC3 : C3ᶜ ∈ 𝒞 := h𝒞.algebra.compl_mem hC.2.2.1
  have hC1 : C1 ∈ 𝒞 := hC.1
  obtain ⟨T, hT, hT1, -, hWT⟩ := h𝒞.convexRanged (C3ᶜ) hC3 univ hCu (subset_univ _) ν hν
    (by rw [h1.W_univ]; exact hν1)
  have hC1T : C1 ⊆ T := (MMC.part3_sub hC).trans hT1
  obtain ⟨C1', hC1', -, hC1'1, hW1⟩ := h𝒞.convexRanged ∅ hCe C1 hC1 (empty_subset _) μ
    (by rw [h1.W_empty]; exact hμ0) hμ
  have hP := MMC.part3_of h𝒞.algebra hC1' hT (hC1'1.trans hC1T)
  refine ⟨C1', T \ C1', Tᶜ, hP, hW1, by rw [compl_compl]; exact hWT, ?_⟩
  intro x hx
  refine ⟨hT1 (MMC.part3_sub2 hC hx), fun hx1 => ?_⟩
  exact (Set.disjoint_left.mp (MMC.part3_disj12 hC)) (hC1'1 hx1) hx

end MMC

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞) (B D : Set S) :
    ((∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (C₃ᶜ) ≤ W D → W C₂ ≤ W A₂) ↔
      (∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W A₁ ≤ W C₁ → W (C₃ᶜ) ≤ W (A₃ᶜ) → W (A₃ᶜ) ≤ W D → W C₂ ≤ W A₂)) ∧
    ((∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W B ≤ W A₁ → W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (A₂ᶜ) ≤ W (C₂ᶜ)) ↔
      (∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W (C₃ᶜ) ≤ W (A₃ᶜ) → W A₁ ≤ W C₁ → W B ≤ W A₁ → W (A₂ᶜ) ≤ W (C₂ᶜ))) := by
  -- data about the A-side partition
  have hA13 : ∀ A₁ A₂ A₃ : Set S, IsPartition3 𝒜 A₁ A₂ A₃ →
      0 ≤ W A₁ ∧ W (A₃ᶜ) ≤ 1 ∧ A₃ᶜ ∈ 𝓔 ∧ A₂ ∈ 𝓔 ∧ A₁ ∈ 𝓔 := by
    intro A₁ A₂ A₃ hA
    have hA3 : A₃ᶜ ∈ 𝒜 := h𝒜.algebra.compl_mem hA.2.2.1
    have e3 : A₃ᶜ ∈ 𝓔 := h𝒜.subset hA3
    have e1 : A₁ ∈ 𝓔 := h𝒜.subset hA.1
    refine ⟨?_, ?_, e3, h𝒜.subset hA.2.1, e1⟩
    · have := h1.W_mono A₁ e1 ∅ h1.events.empty_mem (empty_subset _)
      rwa [h1.W_empty] at this
    · have := h1.W_mono univ h1.events.univ_mem _ e3 (subset_univ _)
      rwa [h1.W_univ] at this
  constructor
  · constructor
    · intro h8 C₁ C₂ C₃ A₁ A₂ A₃ hC hA hle h3 hD
      obtain ⟨a0, a3, -, -, -⟩ := hA13 A₁ A₂ A₃ hA
      obtain ⟨C1', C2', C3', hC', hW1, hW3, hsub⟩ :=
        MMC.refine_part h1 h𝒞 hC (W A₁) (W (A₃ᶜ)) a0 hle h3 a3
      have := h8 C1' C2' C3' A₁ A₂ A₃ hC' hA hW1.symm hW3.symm (hW3.le.trans hD)
      exact (MMC.mono_ev h1 h𝒞 (hC.2.1) hC'.2.1 hsub).trans this
    · intro hA1 C₁ C₂ C₃ A₁ A₂ A₃ hC hA h1' h3 hD
      exact hA1 C₁ C₂ C₃ A₁ A₂ A₃ hC hA h1'.le h3.ge (h3.le.trans hD)
  · constructor
    · intro h9 C₁ C₂ C₃ A₁ A₂ A₃ hC hA h3 hle hB
      obtain ⟨a0, a3, -, -, -⟩ := hA13 A₁ A₂ A₃ hA
      obtain ⟨C1', C2', C3', hC', hW1, hW3, hsub⟩ :=
        MMC.refine_part h1 h𝒞 hC (W A₁) (W (A₃ᶜ)) a0 hle h3 a3
      have := h9 C1' C2' C3' A₁ A₂ A₃ hC' hA hB hW1.symm hW3.symm
      refine this.trans ?_
      have e2 : C₂ ∈ 𝓔 := h𝒞.subset hC.2.1
      have e2' : C2' ∈ 𝓔 := h𝒞.subset hC'.2.1
      exact h1.W_mono _ (h1.events.compl_mem e2) _ (h1.events.compl_mem e2')
        (compl_subset_compl.mpr hsub)
    · intro hA2 C₁ C₂ C₃ A₁ A₂ A₃ hC hA hB h1' h3
      exact hA2 C₁ C₂ C₃ A₁ A₂ A₃ hC hA h3.ge h1'.le hB
