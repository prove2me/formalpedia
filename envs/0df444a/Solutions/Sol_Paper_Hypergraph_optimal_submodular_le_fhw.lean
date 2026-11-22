-- Prove2me | solution 1 for Paper.Hypergraph.optimal_submodular_le_fhw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:11.98552+00:00
-- url     : https://prove2.me/submissions/e63d29f8-08df-48cd-b7ff-0d4b9405aeb9

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth
import Theorems.Thm_Paper_Hypergraph_submodular_le_setCoverCost

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {b : Finset ℕ → ℝ}
    (hb : H.SubmodularWeight b) : H.optimalWidth b ≤ H.fhw := by
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  have hn : ∀ S ⊆ H.vertices, 0 ≤ b S := by
    intro S hS
    have h := hb.2.1 ∅ (empty_subset _) S hS (empty_subset _)
    simpa [hb.1] using h
  apply (H.optimalWidth_le_bagWidth b hn D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact (H.submodular_le_setCoverCost hb (D.bag_subset t)).trans
    (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)
end Paper.Hypergraph
