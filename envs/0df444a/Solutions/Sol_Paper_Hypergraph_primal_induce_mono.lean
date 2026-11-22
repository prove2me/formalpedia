-- Prove2me | solution 1 for Paper.Hypergraph.primal_induce_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:51.603717+00:00
-- url     : https://prove2.me/submissions/3438b90a-112f-4ea8-9e7e-377d8b936740

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
theorem _root_.solution (H : Hypergraph) {U W : Finset ℕ} (hUW : U ⊆ W) :
    (H.induce U).primal ≤ (H.induce W).primal := by
  rintro u v ⟨hne, e, he, hue, hve⟩
  refine ⟨hne, e, mem_filter.mpr ⟨(mem_filter.mp he).1, u, ?_⟩, ?_, ?_⟩
  all_goals first
    | exact mem_inter.mpr ⟨(mem_inter.mp hue).1, hUW (mem_inter.mp hue).2⟩
    | exact mem_inter.mpr ⟨(mem_inter.mp hve).1, hUW (mem_inter.mp hve).2⟩
end Paper.Hypergraph
