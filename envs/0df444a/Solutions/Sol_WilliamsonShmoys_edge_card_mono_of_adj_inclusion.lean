-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_mono_of_adj_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:58:22.411334+00:00
-- url     : https://prove2.me/submissions/aea947c9-62e8-4182-8fb0-8fd412858b37

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hAdj : forall u v, G.Adj u v -> H.Adj u v) :
    G.edgeSet.ncard <= H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr fun _ _ h => hAdj _ _ h) (Set.toFinite _)
