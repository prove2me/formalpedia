-- Prove2me | solution 1 for Paper.Hypergraph.degeneracy_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:53.954733+00:00
-- url     : https://prove2.me/submissions/21f06e57-73b9-457e-b27a-c3e7dfeb541d

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.degeneracy := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  have hd : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ z ∈ S, (S.filter (H.incidence.Adj z)).card ≤ H.degeneracy := by
    refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
      ∃ z ∈ S, (S.filter (H.incidence.Adj z)).card ≤ d}) ?_
    refine ⟨H.incidenceVertices.card, ?_⟩
    intro S hS hS'
    obtain ⟨z, hz⟩ := hS'
    exact ⟨z, hz, (card_filter_le _ _).trans (card_le_card hS)⟩
  have hsub : {Sum.inl v, Sum.inr e} ⊆ H.incidenceVertices := by
    simp [insert_subset_iff, singleton_subset_iff, incidenceVertices, hv, he]
  obtain ⟨z, hz, hdeg⟩ := hd _ hsub (by simp)
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · apply (Nat.succ_le_of_lt (Finset.card_pos.mpr ?_)).trans hdeg
    exact ⟨Sum.inr e, Finset.mem_filter.mpr ⟨by simp, by exact ⟨he, hve⟩⟩⟩
  · apply (Nat.succ_le_of_lt (Finset.card_pos.mpr ?_)).trans hdeg
    exact ⟨Sum.inl v, Finset.mem_filter.mpr ⟨by simp, by exact ⟨he, hve⟩⟩⟩
end Paper.Hypergraph
