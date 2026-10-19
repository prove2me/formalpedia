-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_isTwoDegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/04b96833-7932-4188-8e9e-03abdb6c2597

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_isTwoDegenerate

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ) :
    IsTwoDegenerate (pairParentSystem baseSize depth).graph :=
  ParentSystem.graph_isTwoDegenerate (pairParentSystem baseSize depth)
end TwoDegenerateGraphs
