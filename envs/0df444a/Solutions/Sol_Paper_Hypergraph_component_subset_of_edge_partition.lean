-- Prove2me | solution 1 for Paper.Hypergraph.component_subset_of_edge_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:37.562866+00:00
-- url     : https://prove2.me/submissions/ed1629be-c33d-45d7-a4cf-aafc2ac8a484

import Definitions.Def_Paper_RoundingCutoff
import Definitions.Def_Paper_RoundingRecursion
import Theorems.Thm_Paper_Hypergraph_walk_stays_in_set
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {R P T K : Finset ℕ}
    (hR : R ⊆ P ∪ T)
    (hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) P ∨ Disjoint (H.edge e) T)
    (hK : K ∈ (H.induce R).components) : K ⊆ P ∨ K ⊆ T := by
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  by_cases hmeet : ∃ u ∈ K, u ∈ P
  · obtain ⟨u, huK, huP⟩ := hmeet
    apply Or.inl
    intro v hvK
    have huv := ((H.induce R).component_mem_iff_reachable hK huK (hKV hvK)).mp hvK
    apply (H.induce R).walk_stays_in_set P _ (hKV huK) huP huv.some
    intro a haP b hb hab
    obtain ⟨_, e, he, hae, hbe⟩ := hab
    have heH := (mem_filter.mp he).1
    have hbPT := hR (mem_inter.mp hb).2
    rcases mem_union.mp hbPT with hbP | hbT
    · exact hbP
    · rcases hsep e heH with hdP | hdT
      · exact (disjoint_left.mp hdP (mem_inter.mp hae).1 haP).elim
      · exact (disjoint_left.mp hdT (mem_inter.mp hbe).1 hbT).elim
  · apply Or.inr
    intro v hvK
    have hvPT := hR (mem_inter.mp (hKV hvK)).2
    rcases mem_union.mp hvPT with hvP | hvT
    · exact (hmeet ⟨v, hvK, hvP⟩).elim
    · exact hvT
end Paper.Hypergraph
