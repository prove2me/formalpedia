-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_for_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:22.490641+00:00
-- url     : https://prove2.me/submissions/5ccb444e-9604-49a9-8fce-674ba9ee994b

import Mathlib

set_option autoImplicit false


theorem solution {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (h : G ≤ K) : G.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h) (Set.toFinite _)
