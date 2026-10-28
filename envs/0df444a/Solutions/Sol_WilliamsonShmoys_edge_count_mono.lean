-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:38:20.44099+00:00
-- url     : https://prove2.me/submissions/2834b822-cf3e-4025-b6be-29cac3020d01

import Mathlib
set_option autoImplicit false


theorem solution {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V) (hLH : L ≤ H) : L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hLH) (Set.toFinite _)
