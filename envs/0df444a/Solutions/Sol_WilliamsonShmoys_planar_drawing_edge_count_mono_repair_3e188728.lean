-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_mono_repair_3e188728
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:28:42.77304+00:00
-- url     : https://prove2.me/submissions/8c54453e-b315-4b41-aa00-28f88facf80a

import Mathlib
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y H : SimpleGraph V)
    (hYH : Y ≤ H) :
    Y.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hYH) (Set.toFinite _)
