-- Prove2me | solution 1 for Paper.Hypergraph.edgeDistance_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:03.845807+00:00
-- url     : https://prove2.me/submissions/2461472f-221d-4b1c-87b4-56afbba816f8

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_vertexDistance_indicator

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (S : Finset ℕ) {e f : ℕ}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance (indicator S) e f =
      if ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
        u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by
  obtain ⟨u₀, hu₀⟩ := H.edge_nonempty e he
  obtain ⟨v₀, hv₀⟩ := H.edge_nonempty f hf
  have hne : {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
      r = H.vertexDistance (indicator S) u v}.Nonempty := ⟨_, u₀, hu₀, v₀, hv₀, rfl⟩
  have hlo : ∀ r ∈ {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
      r = H.vertexDistance (indicator S) u v}, 0 ≤ r := by
    rintro r ⟨u, hu, v, hv, rfl⟩
    rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv)]
    split_ifs <;> norm_num
  unfold edgeDistance
  split_ifs with hh
  · obtain ⟨u, hu, v, hv, huv⟩ := hh
    apply le_antisymm
    · refine csInf_le ⟨0, hlo⟩ ⟨u, hu, v, hv, ?_⟩
      rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv), if_pos huv]
    · exact le_csInf hne hlo
  · have hone : ∀ u ∈ H.edge e, ∀ v ∈ H.edge f, H.vertexDistance (indicator S) u v = 1 := by
      intro u hu v hv
      rw [H.vertexDistance_indicator S (H.edge_subset e he hu) (H.edge_subset f hf hv)]
      exact if_neg (fun h => hh ⟨u, hu, v, hv, h⟩)
    apply le_antisymm
    · exact csInf_le ⟨0, hlo⟩ ⟨u₀, hu₀, v₀, hv₀, (hone u₀ hu₀ v₀ hv₀).symm⟩
    · refine le_csInf hne ?_
      rintro r ⟨u, hu, v, hv, rfl⟩
      rw [hone u hu v hv]
end Paper.Hypergraph
