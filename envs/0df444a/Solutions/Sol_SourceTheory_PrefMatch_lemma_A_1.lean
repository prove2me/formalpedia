-- Prove2me | solution 1 for SourceTheory.PrefMatch.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:27:44.947648+00:00
-- url     : https://prove2.me/submissions/7f0c18a5-73a6-4905-8066-27a45f46615e

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set SourceTheory.Uniform

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞) :
    IsPreferredTo W 𝒞 𝒜 ↔ ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W C₁ ≤ W A₁ → W (A₁ᶜ) ≤ W (C₁ᶜ) := by
  constructor
  · intro hP C₁ hC A₁ hA hle
    have hC𝓔 : C₁ ∈ 𝓔 := h𝒞.subset hC
    have h0 : W ∅ ≤ W C₁ := h1.W_mono C₁ hC𝓔 ∅ h1.events.empty_mem (empty_subset _)
    have h0' : W ∅ ≤ W C₁ := h0
    obtain ⟨B, hB, -, hBA, hBW⟩ := h𝒜.convexRanged ∅ h𝒜.algebra.empty_mem A₁ hA (empty_subset _)
      (W C₁) h0' hle
    have h2 := hP C₁ hC B hB hBW
    have h3 : W (A₁ᶜ) ≤ W (Bᶜ) :=
      h1.W_mono (Bᶜ) (h1.events.compl_mem (h𝒜.subset hB)) (A₁ᶜ)
        (h1.events.compl_mem (h𝒜.subset hA)) (compl_subset_compl.mpr hBA)
    exact h3.trans h2
  · intro hP C₁ hC A₁ hA heq
    exact hP C₁ hC A₁ hA heq.ge
