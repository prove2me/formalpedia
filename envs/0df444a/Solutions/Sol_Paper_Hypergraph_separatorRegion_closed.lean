-- Prove2me | solution 1 for Paper.Hypergraph.separatorRegion_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:43.452229+00:00
-- url     : https://prove2.me/submissions/d6c6fb7d-5924-43e1-a115-e034549a5ca5

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (A S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.separatorRegion A S) (hv : v ∈ H.vertices \ S)
    (huv : H.primal.Adj u v) : v ∈ H.separatorRegion A S := by
  obtain ⟨huV, a, ha, hau⟩ := mem_filter.mp hu
  have hadj := (H.primal_induce_adj (H.vertices \ S) huV hv).mpr huv
  exact mem_filter.mpr ⟨hv, a, ha, hau.trans hadj.reachable⟩
end Paper.Hypergraph
