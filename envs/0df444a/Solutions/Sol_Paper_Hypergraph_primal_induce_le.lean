-- Prove2me | solution 1 for Paper.Hypergraph.primal_induce_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:25.276654+00:00
-- url     : https://prove2.me/submissions/8067da0b-6506-4acf-81ba-9fa86739823d

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
theorem _root_.solution (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).primal ≤ H.primal := by
  rintro u v ⟨hne, e, he, hue, hve⟩
  exact ⟨hne, e, (mem_filter.mp he).1, (mem_inter.mp hue).1, (mem_inter.mp hve).1⟩
end Paper.Hypergraph
