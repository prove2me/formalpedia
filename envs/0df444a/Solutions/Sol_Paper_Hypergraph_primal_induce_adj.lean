-- Prove2me | solution 1 for Paper.Hypergraph.primal_induce_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:15.316578+00:00
-- url     : https://prove2.me/submissions/4078e2c6-204c-4bb2-8d10-7fab02af2bbf

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (W : Finset ℕ) {u v : ℕ}
    (hu : u ∈ W) (hv : v ∈ W) :
    (H.induce W).primal.Adj u v ↔ H.primal.Adj u v := by
  constructor
  · rintro ⟨huv, e, he, hue, hve⟩
    exact ⟨huv, e, (mem_filter.mp he).1, (mem_inter.mp hue).1, (mem_inter.mp hve).1⟩
  · rintro ⟨huv, e, he, hue, hve⟩
    exact ⟨huv, e, mem_filter.mpr ⟨he, ⟨u, mem_inter.mpr ⟨hue, hu⟩⟩⟩,
      mem_inter.mpr ⟨hue, hu⟩, mem_inter.mpr ⟨hve, hv⟩⟩
end Paper.Hypergraph
