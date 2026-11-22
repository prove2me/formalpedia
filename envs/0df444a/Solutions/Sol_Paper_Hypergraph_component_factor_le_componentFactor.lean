-- Prove2me | solution 1 for Paper.Hypergraph.component_factor_le_componentFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:59.352938+00:00
-- url     : https://prove2.me/submissions/12a0cb67-56c9-483a-ba89-7aa070c9e21d

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
theorem _root_.solution (H : Hypergraph) {C : Finset ℕ}
    (hC : C ∈ H.components) : (H.induce C).structuralFactor ≤ H.componentFactor := by
  have hfin : {r : ℝ | ∃ C ∈ H.components,
      r = min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))}.Finite := by
    apply Set.Finite.subset (H.components.finite_toSet.image
      (fun C => min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))))
    rintro r ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  have hle := le_csSup (hfin.insert 0).bddAbove (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩)
  unfold structuralFactor componentFactor
  linarith
end Paper.Hypergraph
