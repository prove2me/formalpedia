-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:50:15.12614+00:00
-- url     : https://prove2.me/submissions/5555efb3-b896-4899-a7f2-2a6eb32356fe

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
