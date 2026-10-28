-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:12:14.191278+00:00
-- url     : https://prove2.me/submissions/d2b90af0-4145-41a5-9860-37524e0c9713

import Mathlib
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
