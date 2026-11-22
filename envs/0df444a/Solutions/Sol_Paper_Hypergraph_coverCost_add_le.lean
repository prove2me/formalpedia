-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:23.635413+00:00
-- url     : https://prove2.me/submissions/bb9d9a74-947f-45ff-b58a-ebf8d1d0812d

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_cover_add

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x z : ℕ → ℝ) :
    H.coverCost (x + z) ≤ H.coverCost x + H.coverCost z := by
  have h : H.coverCost (x + z) - H.coverCost z ≤ H.coverCost x := by
    apply H.le_coverCost
    intro y hy
    have h' : H.coverCost (x + z) - ∑ e ∈ H.edges, y e ≤ H.coverCost z := by
      apply H.le_coverCost
      intro u hu
      have := H.coverCost_le (H.cover_add hy hu)
      simp only [Pi.add_apply, sum_add_distrib] at this
      linarith
    linarith
  linarith
end Paper.Hypergraph
