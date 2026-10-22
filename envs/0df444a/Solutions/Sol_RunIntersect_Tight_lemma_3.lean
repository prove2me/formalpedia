-- Prove2me | solution 1 for RunIntersect.Tight.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:07.422511+00:00
-- url     : https://prove2.me/submissions/ad4a1229-216b-4c80-b37e-696096bc1275

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting
set_option autoImplicit false
open RunIntersect.Tight

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (G : RunIntersect.Tight.Hypergraph α) (W : Finset α) (hW : W ⊆ G.V) :
    (∀ t, (∃ v e, IsBetaCycle (subHg G W) t v e) → ∃ v e, IsBetaCycle G t v e) ∧
      (IsBetaAcyclic G → IsBetaAcyclic (subHg G W)) := by
  have key : ∀ (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α), IsBetaCycle (subHg G W) t v e →
      ∃ (v' : Fin t → α) (e' : Fin t → Finset α), IsBetaCycle G t v' e' := by
    intro t v e he
    obtain ⟨h3, hvi, hei, hvV, heE, hmem⟩ := he
    have hex : ∀ i, ∃ f ∈ G.E, f ∩ W = e i := by
      intro i
      have := heE i
      simp only [subHg, Finset.mem_filter, Finset.mem_image] at this
      obtain ⟨⟨f, hf, hfe⟩, -⟩ := this
      exact ⟨f, hf, hfe⟩
    choose f hfE hfW using hex
    refine ⟨v, f, h3, hvi, ?_, ?_, hfE, ?_⟩
    · intro i j hij
      apply hei
      rw [← hfW i, ← hfW j, hij]
    · intro i
      exact hW (hvV i)
    · intro i j
      rw [← hmem i j, ← hfW j]
      have hvW : v i ∈ W := hvV i
      simp [Finset.mem_inter, hvW]
  exact ⟨fun t ⟨v, e, h⟩ => by
      obtain ⟨v', e', h'⟩ := key t v e h
      exact ⟨v', e', h'⟩, fun hG t v e hc => by
    obtain ⟨v', e', h⟩ := key t v e hc
    exact hG t v' e' h⟩
