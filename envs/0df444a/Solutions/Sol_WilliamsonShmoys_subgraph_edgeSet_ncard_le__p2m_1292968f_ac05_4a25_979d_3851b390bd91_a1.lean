-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:42.982048+00:00
-- url     : https://prove2.me/submissions/d1696cec-fcfc-422c-98c2-cad290927f1e

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
