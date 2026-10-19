-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/780cd895-c7cb-46af-8701-5ddd4c60b485

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_isBipartite

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph.IsBipartite :=
  ParentSystem.graph_isBipartite (pairParentSystem baseSize depth)
end TwoDegenerateGraphs
