-- Prove2me | solution 1 for Paper.Hypergraph.le_coverCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:01.921028+00:00
-- url     : https://prove2.me/submissions/db998f9a-9469-4a16-8acc-f7804e72ed62

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_exists

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) {r : ℝ}
    (h : ∀ y, H.Cover x y → r ≤ ∑ e ∈ H.edges, y e) : r ≤ H.coverCost x := by
  obtain ⟨y, hy⟩ := H.cover_exists x
  refine le_csInf ⟨_, y, hy, rfl⟩ ?_
  rintro z ⟨y', hy', rfl⟩
  exact h y' hy'
end Paper.Hypergraph
