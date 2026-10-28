-- Prove2me | solution 1 for SimpleGraph.edgeSet_ncard_mono_for_4be75fe8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:46:59.433363+00:00
-- url     : https://prove2.me/submissions/a8515b6c-f1a5-4fdb-bc7b-57b757e8b30f

import Mathlib


theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
