-- Prove2me | solution 1 for Paper.Hypergraph.modularValue_submodular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:37.699318+00:00
-- url     : https://prove2.me/submissions/4dc18cbf-e7d3-471a-96c7-365f97059da9

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
theorem _root_.solution (H : Hypergraph) {w : ℕ → ℝ}
    (hw : H.ModularWeight w) : H.SubmodularWeight (modularValue w) := by
  refine ⟨by simp [modularValue], ?_, ?_, hw.2⟩
  · intro A hA B hB hAB
    exact sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ => hw.1 v)
  · intro A hA B hB
    exact sum_union_inter.le
end Paper.Hypergraph
