-- Prove2me | solution 1 for Paper.Hypergraph.restrictDemand_cost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:05.975831+00:00
-- url     : https://prove2.me/submissions/0321fdaa-e2af-4546-a9a8-cb84dc61100e

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
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.coverCost (restrictDemand x A) ≤ H.coverCost (restrictDemand x B) := by
  apply H.coverCost_mono
  intro v hv
  by_cases ha : v ∈ A
  · simp [restrictDemand, ha, hAB ha]
  · simp only [restrictDemand, if_neg ha]
    split_ifs <;> first | exact hx v hv | exact le_rfl
end Paper.Hypergraph
