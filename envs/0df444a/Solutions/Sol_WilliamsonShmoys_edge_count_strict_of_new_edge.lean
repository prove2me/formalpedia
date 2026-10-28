-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_strict_of_new_edge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:27:04.675537+00:00
-- url     : https://prove2.me/submissions/492c888e-6bfc-477e-b408-1db560b758d1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (u v : V)
    (hHK : H ≤ K)
    (hSeparated : ¬ H.Reachable u v)
    (hNew : K.Adj u v) :
    H.edgeSet.ncard < K.edgeSet.ncard := by
  have hlt : H < K := lt_of_le_of_ne hHK (by
    rintro rfl; exact hSeparated hNew.reachable)
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt) (Set.toFinite _)
