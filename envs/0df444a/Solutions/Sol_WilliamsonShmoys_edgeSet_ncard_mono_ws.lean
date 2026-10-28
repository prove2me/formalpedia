-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_ws
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:55:02.800056+00:00
-- url     : https://prove2.me/submissions/9a474e7f-1a17-41c7-8124-7f87042167fa

import Mathlib

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 hGH) (Set.toFinite _)
