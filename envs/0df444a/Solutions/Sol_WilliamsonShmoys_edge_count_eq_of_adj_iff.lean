-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:43:19.596277+00:00
-- url     : https://prove2.me/submissions/d0122f7a-d4d2-4b4f-a849-71fae5196080

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hAdj : ∀ u v, G.Adj u v ↔ K.Adj u v) :
    G = K := by
  ext u v; exact hAdj u v
