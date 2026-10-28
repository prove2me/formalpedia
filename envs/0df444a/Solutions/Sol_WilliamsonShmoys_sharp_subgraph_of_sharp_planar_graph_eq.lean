-- Prove2me | solution 1 for WilliamsonShmoys.sharp_subgraph_of_sharp_planar_graph_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:02:02.263311+00:00
-- url     : https://prove2.me/submissions/4f9cd666-02a7-4894-8370-edf3532a6521

import Mathlib


theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hH : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (hK : K.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    H = K := by
  have hs : H.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.2 hHK
  have he : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le hs (by omega) (Set.toFinite _)
  exact SimpleGraph.edgeSet_inj.1 he
