-- Prove2me | solution 1 for Paper.Hypergraph.TreeDecomposition.walk_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:15.522279+00:00
-- url     : https://prove2.me/submissions/8957e16d-2152-4e91-8656-d45ffa7c0252

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_TreeDecomposition_same_vertex_avoiding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
namespace TreeDecomposition
theorem _root_.solution {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v w : ℕ}
    (p : (H.induce (H.vertices \ D.bag t)).primal.Walk v w)
    (hv : v ∈ (H.induce (H.vertices \ D.bag t)).vertices)
    {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : w ∈ D.bag b)
    (hat : a ≠ t) (hbt : b ≠ t) :
    (D.tree.induce {s | s ≠ t}).Reachable ⟨a, hat⟩ ⟨b, hbt⟩ := by
  induction p generalizing a with
  | nil =>
    exact D.same_vertex_avoiding t (mem_inter.mp hv).1
      (mem_sdiff.mp (mem_inter.mp hv).2).2 ha hb
  | @cons v z w hvz p ih =>
    obtain ⟨e, he, hve, hze⟩ := hvz.2
    obtain ⟨c, hc⟩ := D.edge_covered e (mem_filter.mp he).1
    have hzc : z ∈ D.bag c := hc (mem_inter.mp hze).1
    have hvct : c ≠ t := fun h => (mem_sdiff.mp (mem_inter.mp hv).2).2
      (h ▸ hc (mem_inter.mp hve).1)
    have hz : z ∈ (H.induce (H.vertices \ D.bag t)).vertices :=
      (H.induce (H.vertices \ D.bag t)).edge_subset e he hze
    exact (D.same_vertex_avoiding t (mem_inter.mp hv).1
      (mem_sdiff.mp (mem_inter.mp hv).2).2 ha (hc (mem_inter.mp hve).1)).trans
      (ih hz hzc hb hvct)
end TreeDecomposition
end Paper.Hypergraph
