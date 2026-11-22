-- Prove2me | solution 1 for Paper.Hypergraph.support_integralSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:50.253681+00:00
-- url     : https://prove2.me/submissions/77e44d46-6f8d-42a8-b002-566fe4079536

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_primal_induce_le
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    H.IntegralSeparator A B (H.vertices.filter fun v => x v ≠ 0) := by
  let S := H.vertices.filter fun v => x v ≠ 0
  refine ⟨filter_subset _ _, ?_⟩
  intro a ha b hb hab
  obtain ⟨p⟩ := hab
  have haV := hA (mem_sdiff.mp ha).1
  have haJ : a ∈ (H.induce (H.vertices \ S)).vertices :=
    mem_inter.mpr ⟨haV, mem_sdiff.mpr ⟨haV, (mem_sdiff.mp ha).2⟩⟩
  have hcost : (∑ v ∈ (p.mapLe (H.primal_induce_le _)).support.toFinset, x v) = 0 := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    apply sum_eq_zero
    intro v hv
    have hvJ := (H.induce (H.vertices \ S)).walk_vertices p haJ v (List.mem_toFinset.mp hv)
    have hnS := (mem_sdiff.mp (mem_inter.mp hvJ).2).2
    by_contra h
    exact hnS (mem_filter.mpr ⟨(mem_inter.mp hvJ).1, h⟩)
  have hd := H.vertexDistance_le_walk (fun v hv => (hx.1 v hv).1) haV
    (p.mapLe (H.primal_induce_le _))
  have hl := hx.2 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1
  rw [hcost] at hd
  linarith
end Paper.Hypergraph
