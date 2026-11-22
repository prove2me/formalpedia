-- Prove2me | solution 1 for Paper.Hypergraph.incidence_order_left_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:30.165896+00:00
-- url     : https://prove2.me/submissions/43f012c0-b666-4a47-a21d-c6fadf04d533

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
    {e : ℕ} (he : e ∈ H.edges) :
    ((H.edge e).filter (fun v => rank (.inr e) < rank (.inl v))).card ≤ H.degeneracy := by
  have heI : Sum.inr e ∈ H.incidenceVertices := by simp [incidenceVertices, he]
  apply le_trans _ (hlater (.inr e) heI)
  rw [← card_map Function.Embedding.inl]
  apply card_le_card
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
  obtain ⟨hve, hrank⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨by simp [incidenceVertices, H.edge_subset e he hve], ⟨he, hve⟩, hrank⟩
end Paper.Hypergraph
