-- Prove2me | solution 1 for Paper.Hypergraph.component_contained_in_induced_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:01.476115+00:00
-- url     : https://prove2.me/submissions/bc03300c-f3c7-4cad-b1fa-9e6aa56cd4a1

import Definitions.Def_Paper_RoundingCutoff
import Definitions.Def_Paper_RoundingRecursion
import Theorems.Thm_Paper_Hypergraph_component_connected
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_induce_induce
import Theorems.Thm_Paper_Hypergraph_primal_induce_mono


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {R T K : Finset ℕ}
    (hK : K ∈ (H.induce R).components) (hKT : K ⊆ T) :
    ∃ L ∈ (H.induce T).components, K ⊆ L := by
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨u, huK, _⟩ := (mem_filter.mp hK).2
  have huT : u ∈ (H.induce T).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hKV huK)).1, hKT huK⟩
  obtain ⟨L, hL, huL⟩ := (H.induce T).exists_component_of_mem huT
  have hconn := (H.induce R).component_connected hK
  have hgraph : ((H.induce R).induce K).primal ≤ (H.induce T).primal := by
    rw [H.induce_induce]
    exact H.primal_induce_mono (inter_subset_right.trans hKT)
  refine ⟨L, hL, ?_⟩
  intro v hvK
  have hvT : v ∈ (H.induce T).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hKV hvK)).1, hKT hvK⟩
  apply ((H.induce T).component_mem_iff_reachable hL huL hvT).mpr
  have hr := hconn.2 u (mem_inter.mpr ⟨hKV huK, huK⟩) v (mem_inter.mpr ⟨hKV hvK, hvK⟩)
  exact ⟨hr.some.mapLe hgraph⟩
end Paper.Hypergraph
