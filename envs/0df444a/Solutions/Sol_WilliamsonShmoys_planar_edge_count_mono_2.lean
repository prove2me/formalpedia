-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:50:51.650995+00:00
-- url     : https://prove2.me/submissions/f2f42a5f-f126-45eb-9187-c93cd26178af

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by 
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
