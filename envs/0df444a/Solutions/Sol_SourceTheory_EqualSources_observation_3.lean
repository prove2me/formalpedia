-- Prove2me | solution 1 for SourceTheory.EqualSources.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:00:50.787351+00:00
-- url     : https://prove2.me/submissions/d939fddc-7341-4d62-a332-73d6fc74924f

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

/-- for a source, any value between `W A` and `W C` (`A ⊆ C` in the source) is attained. -/
lemma mono_ev {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop} {U : Γ → ℝ}
    {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒮 : Set (Set S)} (h𝒮 : IsSource 𝓔 W 𝒮)
    {A C : Set S} (hA : A ∈ 𝒮) (hC : C ∈ 𝒮) (hAC : A ⊆ C) : W A ≤ W C :=
  h1.W_mono C (h𝒮.subset hC) A (h𝒮.subset hA) hAC

end MMC

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒮 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒮 : SourceTheory.Uniform.IsSource 𝓔 W 𝒮)
    (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞) :
    (SourceTheory.Uniform.IsPreferredTo W 𝒮 𝒜 → SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒮 → SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜) ∧
    (∀ B₁ ∈ 𝓔, ∀ D₁ ∈ 𝓔, ∀ B₂ ∈ 𝓔, ∀ D₂ ∈ 𝓔,
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒮 B₁ D₁ → SourceTheory.Uniform.IsMoreInsensitive W 𝒮 𝒞 B₂ D₂ →
      ∀ B ∈ 𝓔, ∀ D ∈ 𝓔, W B₁ ≤ W B → W B₂ ≤ W B → W D ≤ W D₁ → W D ≤ W D₂ →
        SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D) := by
  have hSe : ∅ ∈ 𝒮 := h𝒮.algebra.empty_mem
  have hSu : (univ : Set S) ∈ 𝒮 := h𝒮.algebra.univ_mem
  constructor
  · intro hSA hCS C1 hC1 A1 hA1 hEq
    have hA1e : A1 ∈ 𝓔 := h𝒜.subset hA1
    obtain ⟨S1, hS1, -, -, hW⟩ := h𝒮.convexRanged ∅ hSe univ hSu (empty_subset _) (W A1)
      (h1.W_mono A1 hA1e ∅ (h1.events.empty_mem) (empty_subset _))
      (h1.W_mono univ h1.events.univ_mem A1 hA1e (subset_univ _))
    have a1 := hSA S1 hS1 A1 hA1 hW.symm
    have a2 := hCS C1 hC1 S1 hS1 (hW.trans hEq)
    exact a1.trans a2
  · intro B₁ hB₁ D₁ hD₁ B₂ hB₂ D₂ hD₂ hi1 hi2 B hB D hD hb1 hb2 hd1 hd2
    intro C1 C2 C3 A1 A2 A3 hC hA
    have hC3 : C3ᶜ ∈ 𝒞 := h𝒞.algebra.compl_mem hC.2.2.1
    have hC1m : C1 ∈ 𝒞 := hC.1
    have hle : W C1 ≤ W (C3ᶜ) := MMC.mono_ev h1 h𝒞 hC1m hC3 (MMC.part3_sub hC)
    have hC3e : C3ᶜ ∈ 𝓔 := h𝒞.subset hC3
    have hC1e : C1 ∈ 𝓔 := h𝒞.subset hC1m
    obtain ⟨T, hT, -, -, hWT⟩ := h𝒮.convexRanged ∅ hSe univ hSu (empty_subset _) (W (C3ᶜ))
      (h1.W_mono _ hC3e ∅ (h1.events.empty_mem) (empty_subset _))
      (h1.W_mono univ h1.events.univ_mem _ hC3e (subset_univ _))
    have hTe : T ∈ 𝓔 := h𝒮.subset hT
    obtain ⟨S1, hS1, -, hS1T, hWS1⟩ := h𝒮.convexRanged ∅ hSe T hT (empty_subset _) (W C1)
      (h1.W_mono _ hC1e ∅ (h1.events.empty_mem) (empty_subset _)) (by rw [hWT]; exact hle)
    have hP := MMC.part3_of h𝒮.algebra hS1 hT hS1T
    have e1 := hi1 S1 (T \ S1) Tᶜ A1 A2 A3 hP hA
    have e2 := hi2 C1 C2 C3 S1 (T \ S1) Tᶜ hC hP
    rw [compl_compl] at e1 e2
    refine ⟨?_, ?_⟩
    · intro hA1C hA3 hCD
      have x1 := e1.1 (hA1C.trans hWS1.symm) (hA3.trans hWT.symm) (by rw [hWT]; exact hCD.trans hd1)
      have x2 := e2.1 hWS1 hWT (hCD.trans hd2)
      exact x2.trans x1
    · intro hBA hA1C hA3
      have y1 := e1.2 (hb1.trans hBA) (hA1C.trans hWS1.symm) (hA3.trans hWT.symm)
      have y2 := e2.2 (hb2.trans (hBA.trans (hA1C.le.trans hWS1.symm.le))) hWS1 hWT
      exact y1.trans y2
