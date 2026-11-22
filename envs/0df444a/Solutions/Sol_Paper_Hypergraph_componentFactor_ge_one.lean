-- Prove2me | solution 1 for Paper.Hypergraph.componentFactor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:45.896435+00:00
-- url     : https://prove2.me/submissions/6358a238-fa2e-4b46-a114-f71a5400275b

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
theorem _root_.solution (H : Hypergraph) : 1 ≤ H.componentFactor := by
  have hfin : {r : ℝ | ∃ C ∈ H.components,
      r = min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))}.Finite := by
    apply Set.Finite.subset (H.components.finite_toSet.image
      (fun C => min ((H.induce C).degeneracy : ℝ)
        (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))))
    rintro r ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  have hzero := le_csSup (hfin.insert 0).bddAbove (Set.mem_insert 0 _)
  unfold componentFactor
  linarith
end Paper.Hypergraph
