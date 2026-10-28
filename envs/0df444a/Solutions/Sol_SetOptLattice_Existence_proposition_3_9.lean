-- Prove2me | solution 1 for SetOptLattice.Existence.proposition_3_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:28:48.150459+00:00
-- url     : https://prove2.me/submissions/4bcef3bb-3ad1-43bf-9b97-39989a27650c

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open Set Filter Topology
open scoped Pointwise

open SetOptLattice.Existence in
theorem solution {X Z : Type*} [Nonempty X] [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : Set X, IsSolution Ψ f ε M := by
  have hE : ∀ a : EReal, a ≠ ⊤ → a < epsBound a ε := by
    intro a ha
    unfold epsBound
    split_ifs with h1 h2
    · exact absurd h2 hε.ne'
    · rw [h1]; exact EReal.bot_lt_coe _
    · rw [← EReal.coe_toReal ha h1, ← EReal.coe_add]
      exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hT : epsBound ⊤ ε = ⊤ := by
    unfold epsBound
    rw [if_neg (by simp)]
    exact EReal.top_add_coe ε
  have key : ∀ ψ ∈ Ψ, ∀ e, infExt ψ (infImage Ψ f univ) < e → ∃ x, infExt ψ (f x) < e := by
    intro ψ hψ e he
    have hle : infExt ψ (⋃₀ (f '' univ)) ≤ infExt ψ (infImage Ψ f univ) := by
      show infExt ψ _ ≤ ⨅ z ∈ clPsi Ψ (⋃₀ (f '' univ)), ψ z
      exact le_iInf₂ fun z hz => hz ψ hψ
    have h2 := lt_of_le_of_lt hle he
    unfold infExt at h2
    rw [iInf_lt_iff] at h2
    obtain ⟨z, hz⟩ := h2
    rw [iInf_lt_iff] at hz
    obtain ⟨hzD, hz⟩ := hz
    obtain ⟨S, hS, hzS⟩ := Set.mem_sUnion.1 hzD
    obtain ⟨x, _, rfl⟩ := hS
    exact ⟨x, lt_of_le_of_lt (biInf_le ψ hzS) hz⟩
  refine ⟨MinSet Ψ f ε, ⟨?_, ?_⟩, subset_rfl⟩
  · obtain ⟨ψ0, hψ0⟩ := hΨne
    by_cases htop : infExt ψ0 (infImage Ψ f univ) = ⊤
    · refine ⟨Classical.arbitrary X, ψ0, hψ0, ?_⟩
      rw [htop, hT]; exact le_top
    · obtain ⟨x, hx⟩ := key ψ0 hψ0 _ (hE _ htop)
      exact ⟨x, ψ0, hψ0, hx.le⟩
  · intro ψ hψ
    by_cases htop : infExt ψ (infImage Ψ f univ) = ⊤
    · rw [htop, hT]; exact le_top
    · obtain ⟨x, hx⟩ := key ψ hψ _ (hE _ htop)
      have hxM : x ∈ MinSet Ψ f ε := ⟨ψ, hψ, hx.le⟩
      have hsub : f x ⊆ infImage Ψ f (MinSet Ψ f ε) := by
        intro z hz φ hφ
        exact biInf_le φ (Set.mem_sUnion.2 ⟨f x, ⟨x, hxM, rfl⟩, hz⟩)
      calc infExt ψ (infImage Ψ f (MinSet Ψ f ε)) ≤ infExt ψ (f x) :=
            biInf_mono fun z hz => hsub hz
        _ ≤ _ := hx.le
