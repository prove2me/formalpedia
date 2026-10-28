-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_of_subgraph_c7059b55_ff77_4f00_a57a_8983712db7a5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:33.730175+00:00
-- url     : https://prove2.me/submissions/5f8f9143-e7ee-4e8d-9791-8e6ca7a8ac51

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hMN : M ≤ N) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMN) (Set.toFinite _)
