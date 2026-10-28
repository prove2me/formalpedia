-- Prove2me | solution 1 for WilliamsonShmoys.le_of_edgeSet_ncard_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:17:12.956019+00:00
-- url     : https://prove2.me/submissions/1551bb8e-c378-4c74-bff7-968ae368869c

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    H ≤ G := by
  have hs : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hGH
  have := Set.eq_of_subset_of_ncard_le hs hcard (Set.toFinite _)
  exact SimpleGraph.edgeSet_subset_edgeSet.mp this.symm.subset
