-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:32:50.769438+00:00
-- url     : https://prove2.me/submissions/f317f263-262b-47e9-8107-3b8c35345812

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

set_option autoImplicit false
open PCSPBLPAff.Characterization

theorem solution {τ : Type} {ar : τ → ℕ} {D B : Type} [Finite B]
    (𝔽 : PCSPBLPAff.Symmetric.RelStruct τ ar D) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (h : ∀ S : Finset D, ∃ σ : D → B,
      ∀ R : τ, ∀ t ∈ 𝔽.rel R, (∀ k, t k ∈ S) → σ ∘ t ∈ 𝔹.rel R) :
    ∃ σ : D → B, PCSPBLPAff.Symmetric.IsHom 𝔽 𝔹 σ := by
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : CompactSpace B := Finite.compactSpace
  let F : Finset D → Set (D → B) := fun S =>
    {σ | ∀ R : τ, ∀ t ∈ 𝔽.rel R, (∀ k, t k ∈ S) → σ ∘ t ∈ 𝔹.rel R}
  have hclosed : ∀ S, IsClosed (F S) := by
    intro S
    have : F S = ⋂ R : τ, ⋂ t : Fin (ar R) → D, ⋂ (_ : t ∈ 𝔽.rel R), ⋂ (_ : ∀ k, t k ∈ S),
        {σ : D → B | σ ∘ t ∈ 𝔹.rel R} := by
      ext σ; simp [F]
    rw [this]
    refine isClosed_iInter fun R => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    have hc : Continuous (fun σ : D → B => σ ∘ t) :=
      continuous_pi fun k => continuous_apply (t k)
    exact (isClosed_discrete (𝔹.rel R)).preimage hc
  have hne : ∀ S, (F S).Nonempty := fun S => h S
  have hdir : Directed (· ⊇ ·) F := by
    intro S S'
    refine ⟨S ∪ S', ?_, ?_⟩
    · intro σ hσ R t ht hS
      exact hσ R t ht (fun k => Finset.mem_union_left _ (hS k))
    · intro σ hσ R t ht hS
      exact hσ R t ht (fun k => Finset.mem_union_right _ (hS k))
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hdir hne
    (fun S => (hclosed S).isCompact) hclosed
  refine ⟨σ, fun R t ht => ?_⟩
  have := Set.mem_iInter.mp hσ (Finset.univ.image t)
  exact this R t ht (fun k => Finset.mem_image_of_mem t (Finset.mem_univ k))
