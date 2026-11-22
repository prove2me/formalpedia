-- Prove2me | solution 1 for Paper.Hypergraph.optimalWidth_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:13.278048+00:00
-- url     : https://prove2.me/submissions/dd462724-859b-43ad-ac20-a8317c580b18

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
theorem _root_.solution (H : Hypergraph) (b : Finset ℕ → ℝ) {L : ℝ}
    (hb : ∀ S ⊆ H.vertices, L ≤ b S) :
    L ≤ H.optimalWidth b ∧ H.optimalWidth b ≤ b H.vertices := by
  have hlo : ∀ r ∈ {r | ∃ n, ∃ D : H.TreeDecomposition n, r = D.bagWidth b},
      L ≤ r := by
    rintro r ⟨n, D, rfl⟩
    exact (hb _ (D.bag_subset 0)).trans
      (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
  constructor
  · exact le_csInf ⟨_, 0, H.oneBag, rfl⟩ hlo
  · calc
      H.optimalWidth b ≤ H.oneBag.bagWidth b :=
        csInf_le ⟨L, hlo⟩ ⟨0, H.oneBag, rfl⟩
      _ = b H.vertices := by simp [TreeDecomposition.bagWidth, oneBag]
end Paper.Hypergraph
