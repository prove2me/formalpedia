-- Prove2me | solution 1 for Paper.Hypergraph.restrictDemand_restrict_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:04.406289+00:00
-- url     : https://prove2.me/submissions/1fdd9255-3d3c-4e61-a95e-2c94bd69bf60

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (x : ℕ → ℝ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    restrictDemand (restrictDemand x B) A = restrictDemand x A := by
  funext v
  by_cases ha : v ∈ A
  · simp [restrictDemand, ha, hAB ha]
  · simp [restrictDemand, ha]
end Paper.Hypergraph
