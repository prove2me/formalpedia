-- Prove2me | solution 1 for WilliamsonShmoys.graph_le_of_le_of_edge_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:41:13.367149+00:00
-- url     : https://prove2.me/submissions/9c535888-4962-4a8a-93ff-85b352eaa8f0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hcard : N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    N ≤ M := by
  have hsub : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_mono hMN
  have heq : M.edgeSet = N.edgeSet := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have : M = N := SimpleGraph.edgeSet_injective heq
  exact this ▸ le_rfl
