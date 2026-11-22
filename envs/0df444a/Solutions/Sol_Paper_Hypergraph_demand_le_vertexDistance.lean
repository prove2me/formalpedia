-- Prove2me | solution 1 for Paper.Hypergraph.demand_le_vertexDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:48.279314+00:00
-- url     : https://prove2.me/submissions/edded584-487b-4565-a5bc-a5fe4e9b7fa3

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x)
    {u v : ℕ} (hu : u ∈ H.vertices) (hv : v ∈ H.vertices) :
    x v ≤ H.vertexDistance x u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact (hx v hv).2
  · apply single_le_sum
    · intro z hz
      exact (hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz))).1
    · exact List.mem_toFinset.mpr p.end_mem_support
end Paper.Hypergraph
