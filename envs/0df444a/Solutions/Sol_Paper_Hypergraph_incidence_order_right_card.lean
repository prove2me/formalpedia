-- Prove2me | solution 1 for Paper.Hypergraph.incidence_order_right_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:19.006656+00:00
-- url     : https://prove2.me/submissions/42f2ade5-f4ae-47da-8fe4-080dcffd0067

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ}
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {v : ℕ} (hv : v ∈ H.vertices) :
    (H.edges.filter (fun e => v ∈ H.edge e ∧ rank (.inl v) < rank (.inr e))).card ≤ H.degeneracy := by
  have hvI : Sum.inl v ∈ H.incidenceVertices := by simp [incidenceVertices, hv]
  apply le_trans _ (hlater (.inl v) hvI)
  rw [← card_map Function.Embedding.inr]
  apply card_le_card
  intro w hw
  obtain ⟨e, he, rfl⟩ := mem_map.mp hw
  obtain ⟨he, hve, hrank⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨by simp [incidenceVertices, he], ⟨he, hve⟩, hrank⟩
end Paper.Hypergraph
