-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_le_of_tight_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:05:52.845305+00:00
-- url     : https://prove2.me/submissions/b812e7da-1c76-4265-9976-333df38ce6c4

import Mathlib
theorem solution
    {V : Type} [Fintype V] {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hHEq : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have := Set.ncard_le_ncard (fun e he => SimpleGraph.edgeSet_mono hGH he) (Set.toFinite H.edgeSet)
  omega
