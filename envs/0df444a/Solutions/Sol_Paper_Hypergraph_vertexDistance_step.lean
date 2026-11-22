-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:08.19959+00:00
-- url     : https://prove2.me/submissions/fa7cede0-ea73-43aa-87d3-9ef40287628a

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_one


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c u v : ℕ}
    (hc : c ∈ H.vertices) (hv : v ∈ H.vertices) (huv : H.primal.Adj u v) :
    H.vertexDistance x c v ≤ H.vertexDistance x c u + x v := by
  suffices h : H.vertexDistance x c v - x v ≤ H.vertexDistance x c u by linarith
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · have := H.vertexDistance_le_one hx hc (v := v)
    have := hx v hv
    linarith
  · have hd := H.vertexDistance_le_walk hx hc (p.concat huv)
    simp only [SimpleGraph.Walk.support_concat, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, union_insert, union_empty] at hd
    by_cases hm : v ∈ p.support.toFinset
    · rw [insert_eq_of_mem hm] at hd
      have := hx v hv
      linarith
    · rw [sum_insert hm] at hd
      linarith
end Paper.Hypergraph
