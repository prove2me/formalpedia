-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_retry2_edge_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:03:42.386007+00:00
-- url     : https://prove2.me/submissions/eba3ef5f-0859-4f4d-adcd-eb76f3bfa888

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hSub : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hSub) (Set.toFinite _)
