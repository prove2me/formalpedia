-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_count_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:45:10.345622+00:00
-- url     : https://prove2.me/submissions/00b2ae93-72b6-4020-a91b-055b1271dc44

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hGH) (Set.toFinite _)
