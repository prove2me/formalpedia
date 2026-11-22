-- Prove2me | solution 1 for Paper.Hypergraph.componentFactor_le_structuralFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:16.822074+00:00
-- url     : https://prove2.me/submissions/45dd5823-7ec7-4ce4-8277-9a1c5632264e

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_structure_hereditary

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) :
    H.componentFactor ≤ H.structuralFactor := by
  unfold componentFactor structuralFactor
  apply add_le_add_right
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨K, hK, rfl⟩)
  · exact le_min (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith))
  · apply min_le_min
    · exact_mod_cast (H.structure_hereditary K).1
    · apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_left (H.structure_hereditary K).2 2
end Paper.Hypergraph
