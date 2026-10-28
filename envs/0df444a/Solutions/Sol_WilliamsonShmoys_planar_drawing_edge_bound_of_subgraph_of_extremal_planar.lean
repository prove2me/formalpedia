-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_of_subgraph_of_extremal_planar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:27:15.067426+00:00
-- url     : https://prove2.me/submissions/8750f399-e5a0-490e-96d0-17215ee06c0a

import Mathlib

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hGH : G ≤ H) (hHE : H.edgeSet.ncard + 6 = 3 * Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
  omega
