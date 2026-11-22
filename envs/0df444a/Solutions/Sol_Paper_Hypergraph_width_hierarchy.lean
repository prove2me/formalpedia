-- Prove2me | solution 1 for Paper.Hypergraph.width_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:47.234853+00:00
-- url     : https://prove2.me/submissions/40040b74-d457-4d9c-a11c-4aa2862d35d6

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_modularValue_submodular
import Theorems.Thm_Paper_Hypergraph_optimal_submodular_le_fhw

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) : H.adw ≤ H.subw ∧ H.subw ≤ H.fhw := by
  have hz : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
  have hbound : ∀ r ∈ {r | ∃ b, H.SubmodularWeight b ∧ r = H.optimalWidth b},
      r ≤ H.fhw := by
    rintro r ⟨b, hb, rfl⟩
    exact H.optimal_submodular_le_fhw hb
  constructor
  · refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    exact le_csSup ⟨H.fhw, hbound⟩ ⟨modularValue w, H.modularValue_submodular hw, rfl⟩
  · exact csSup_le ⟨_, _, H.modularValue_submodular hz, rfl⟩ hbound
end Paper.Hypergraph
