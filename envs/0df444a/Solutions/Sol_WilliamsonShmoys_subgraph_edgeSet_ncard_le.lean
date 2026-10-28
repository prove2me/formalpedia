-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeSet_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:10:37.070617+00:00
-- url     : https://prove2.me/submissions/9e7c5bcf-dd6c-4fd2-9774-4d3740a29782

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (M H : SimpleGraph V) (hMH : M ≤ H) :
    Set.ncard M.edgeSet ≤ Set.ncard H.edgeSet :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMH) (Set.toFinite _)
