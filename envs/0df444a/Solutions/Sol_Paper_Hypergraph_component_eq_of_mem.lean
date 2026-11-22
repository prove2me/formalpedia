-- Prove2me | solution 1 for Paper.Hypergraph.component_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:32.341098+00:00
-- url     : https://prove2.me/submissions/af39eb75-d30a-4293-986f-0fda0368dc8a

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {C K : Finset ℕ}
    (hC : C ∈ H.components) (hK : K ∈ H.components) {v : ℕ}
    (hvC : v ∈ C) (hvK : v ∈ K) : C = K := by
  have hCV := mem_powerset.mp (mem_filter.mp hC).1
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  ext w
  by_cases hw : w ∈ H.vertices
  · rw [H.component_mem_iff_reachable hC hvC hw, H.component_mem_iff_reachable hK hvK hw]
  · exact iff_of_false (fun h => hw (hCV h)) (fun h => hw (hKV h))
end Paper.Hypergraph
