-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_9f95e338
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:10:07.693092+00:00
-- url     : https://prove2.me/submissions/ba0f1317-d39f-44b1-8637-d6054576b221

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] (H T : SimpleGraph V) (hsub : H ≤ T) :
    H.edgeSet.ncard ≤ T.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hsub) (Set.toFinite _)
