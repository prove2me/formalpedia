-- Prove2me | solution 1 for RunIntersect.Strict.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:37:44.861745+00:00
-- url     : https://prove2.me/submissions/2a591670-957e-42d1-82af-564e2645c4e4

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting
set_option autoImplicit false
open RunIntersect.Strict

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (G : RunIntersect.Strict.Hypergraph α) (W : Finset α)
    (hW : W ⊆ G.V) :
    (∀ (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α), IsBetaCycle (subHg G W) t v e →
        ∃ (v' : Fin t → α) (e' : Fin t → Finset α), IsBetaCycle G t v' e') ∧
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
  exact ⟨key, fun hG t v e hc => by
    obtain ⟨v', e', h⟩ := key t v e hc
    exact hG t v' e' h⟩
