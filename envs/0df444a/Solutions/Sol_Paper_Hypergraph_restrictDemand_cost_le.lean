-- Prove2me | solution 1 for Paper.Hypergraph.restrictDemand_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:09.882939+00:00
-- url     : https://prove2.me/submissions/1ea56350-4cc7-459e-bda9-3e4cde4e3e6b

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_coverCost_mono


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (A : Finset ℕ) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost x := by
  apply H.coverCost_mono
  intro v hv
  dsimp [restrictDemand]
  split_ifs <;> first | exact le_rfl | exact hx v hv
end Paper.Hypergraph
