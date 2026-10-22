-- Prove2me | solution 1 for SourceTheory.Uniform.eq_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:28:14.346695+00:00
-- url     : https://prove2.me/submissions/c035b451-3db3-407d-bbdf-6be417ec1e35

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set SourceTheory.Uniform

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (hpref : IsPreferredTo W 𝒮 𝒮) :
    ∀ A ∈ 𝒮, ∀ C ∈ 𝒮, W C ≤ W A ↔ W (Aᶜ) ≤ W (Cᶜ) := by
  -- weak form (7) of source preference, via convex rangedness
  have key : ∀ C₁ ∈ 𝒮, ∀ A₁ ∈ 𝒮, W C₁ ≤ W A₁ → W (A₁ᶜ) ≤ W (C₁ᶜ) := by
    intro C₁ hC A₁ hA hle
    have h0 : W ∅ ≤ W C₁ := h1.W_mono C₁ (h𝒮.subset hC) ∅ h1.events.empty_mem (empty_subset _)
    obtain ⟨B, hB, -, hBA, hBW⟩ := h𝒮.convexRanged ∅ h𝒮.algebra.empty_mem A₁ hA (empty_subset _)
      (W C₁) h0 hle
    have h2 := hpref C₁ hC B hB hBW
    have h3 : W (A₁ᶜ) ≤ W (Bᶜ) :=
      h1.W_mono (Bᶜ) (h1.events.compl_mem (h𝒮.subset hB)) (A₁ᶜ)
        (h1.events.compl_mem (h𝒮.subset hA)) (compl_subset_compl.mpr hBA)
    exact h3.trans h2
  intro A hA C hC
  constructor
  · exact key C hC A hA
  · intro h
    have := key (Aᶜ) (h𝒮.algebra.compl_mem hA) (Cᶜ) (h𝒮.algebra.compl_mem hC) h
    simpa using this
