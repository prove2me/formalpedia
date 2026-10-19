-- Prove2me | solution 1 for TwoDegenerateGraphs.ParentSystem.graph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/68b7c000-7f5b-41d3-ba74-98f5c65109ca

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.ParentSystem
namespace TwoDegenerateGraphs.ParentSystem
theorem _root_.solution {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by
  rfl
end TwoDegenerateGraphs.ParentSystem
