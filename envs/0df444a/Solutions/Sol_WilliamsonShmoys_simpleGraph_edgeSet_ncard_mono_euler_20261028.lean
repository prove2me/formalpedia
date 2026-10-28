-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_euler_20261028
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:23:42.670849+00:00
-- url     : https://prove2.me/submissions/e1aa598e-0815-4ca8-bf2f-06a357215a72

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (H G : SimpleGraph V)
    (hHG : H ≤ G) :
    H.edgeSet.ncard ≤ G.edgeSet.ncard := by
  classical
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHG) (Set.toFinite _)
