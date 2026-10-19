-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/b4b6c3ba-3f19-44f3-aa81-dc5f2f00e9fd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairLayer_reaches_base
import Theorems.Thm_TwoDegenerateGraphs_pairBaseVertices_reachable

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairParentSystem baseSize depth).graph.Connected := by
  let root : Fin baseSize := ⟨0, hbase⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := pairLayer_reaches_base baseSize depth i hi v
  exact (pairBaseVertices_reachable baseSize depth hdepth root a).trans ha.symm
end TwoDegenerateGraphs
