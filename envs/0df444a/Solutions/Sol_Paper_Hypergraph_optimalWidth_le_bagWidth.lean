-- Prove2me | solution 1 for Paper.Hypergraph.optimalWidth_le_bagWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:41.61017+00:00
-- url     : https://prove2.me/submissions/04c5a33a-ddcd-4c40-8fab-920f9a028ace

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
theorem _root_.solution (H : Hypergraph) (b : Finset ℕ → ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) {n : ℕ} (D : H.TreeDecomposition n) :
    H.optimalWidth b ≤ D.bagWidth b := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, D, rfl⟩
  rintro r ⟨m, D', rfl⟩
  exact (hb _ (D'.bag_subset 0)).trans
    (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
end Paper.Hypergraph
