-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_edge_count_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:14:36.038496+00:00
-- url     : https://prove2.me/submissions/049ac89a-e752-487c-a0a6-346adc039a55

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h)