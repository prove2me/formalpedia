-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_of_subgraph_1794ae85
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:33:11.898133+00:00
-- url     : https://prove2.me/submissions/01b7f949-e153-42cc-8f12-4d4fc91a07af

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
