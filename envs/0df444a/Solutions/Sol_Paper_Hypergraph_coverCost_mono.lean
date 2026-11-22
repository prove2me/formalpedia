-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:41.420026+00:00
-- url     : https://prove2.me/submissions/cc1c5a04-4183-424e-a752-8dcb7a3372de

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_le_coverCost

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x z : ℕ → ℝ}
    (h : ∀ v ∈ H.vertices, x v ≤ z v) : H.coverCost x ≤ H.coverCost z := by
  apply H.le_coverCost
  intro y hy
  exact H.coverCost_le ⟨hy.1, fun v hv => (h v hv).trans (hy.2 v hv)⟩
end Paper.Hypergraph
