-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_count_of_exact_supergraph_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:44:51.2799+00:00
-- url     : https://prove2.me/submissions/54d8688c-1db4-4ea5-9f71-e44c4f85a005

import Mathlib

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
  omega
