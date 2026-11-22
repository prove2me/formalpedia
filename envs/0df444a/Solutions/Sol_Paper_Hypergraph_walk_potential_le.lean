-- Prove2me | solution 1 for Paper.Hypergraph.walk_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:03.911148+00:00
-- url     : https://prove2.me/submissions/1e8dd6e2-33b3-47bf-af9b-43d027c06e7d

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {f z : ℕ → ℝ}
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → f v ≤ f u + z v)
    {u v : ℕ} (hu : u ∈ H.vertices) (p : H.primal.Walk u v) (hp : p.IsPath) :
    f v ≤ f u + (∑ w ∈ p.support.toFinset, z w) - z u := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
    have hw := H.walk_vertices (.cons huw p) hu w (by simp)
    have hp' := (SimpleGraph.Walk.cons_isPath_iff huw p).mp hp
    have hi := ih hw hp'.1
    have hs := hstep u hu w hw huw
    simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
    rw [sum_insert (by simpa using hp'.2)]
    linarith
end Paper.Hypergraph
