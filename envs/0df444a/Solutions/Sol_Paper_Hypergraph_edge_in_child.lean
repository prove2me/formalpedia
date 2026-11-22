-- Prove2me | solution 1 for Paper.Hypergraph.edge_in_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:29.581808+00:00
-- url     : https://prove2.me/submissions/fab9430b-9d66-49fe-afe2-5dabfcbc59e0

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_edge_subset_component

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {W B : Finset ℕ}
    {e : ℕ} (he : e ∈ (H.induce W).edges) (hn : ¬ (H.induce W).edge e ⊆ B) :
    ∃ K ∈ (H.induce (W \ B)).components,
      (H.induce W).edge e ⊆ K ∪ (H.induce W).boundary B K := by
  obtain ⟨v, hve, hvB⟩ := not_subset.mp hn
  have hvJ := (H.induce W).edge_subset e he hve
  have hvR : v ∈ (H.induce (W \ B)).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp hvJ).1, mem_sdiff.mpr ⟨(mem_inter.mp hvJ).2, hvB⟩⟩
  obtain ⟨K, hK, hvK⟩ := (H.induce (W \ B)).exists_component_of_mem hvR
  refine ⟨K, hK, ?_⟩
  intro z hze
  by_cases hzB : z ∈ B
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨hzB, v, hvK, ?_⟩
    exact ⟨fun hzv => hvB (hzv ▸ hzB), e, he, hze, hve⟩
  · apply mem_union_left
    have heR : e ∈ (H.induce (W \ B)).edges :=
      mem_filter.mpr ⟨(mem_filter.mp he).1,
        v, mem_inter.mpr ⟨(mem_inter.mp hve).1, (mem_inter.mp hvR).2⟩⟩
    exact (H.induce (W \ B)).edge_subset_component hK heR
      (mem_inter.mpr ⟨(mem_inter.mp hve).1, (mem_inter.mp hvR).2⟩) hvK
      (mem_inter.mpr ⟨(mem_inter.mp hze).1, mem_sdiff.mpr ⟨(mem_inter.mp hze).2, hzB⟩⟩)
end Paper.Hypergraph
