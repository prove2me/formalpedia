-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_graph_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:37:08.426564+00:00
-- url     : https://prove2.me/submissions/4ef635a6-49fd-492d-b0d6-6fbfecadc327

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L) (hLK : L ≤ K) :
    K.edgeSet.ncard = L.edgeSet.ncard := by
  rw [le_antisymm hKL hLK]
