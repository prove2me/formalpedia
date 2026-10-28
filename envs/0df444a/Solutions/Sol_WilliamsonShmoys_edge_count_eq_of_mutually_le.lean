-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_mutually_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:48:05.503825+00:00
-- url     : https://prove2.me/submissions/efd9eab1-c5d8-4ccf-bd37-2cbfbe213855

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L)
    (hLK : L ≤ K) :
    K.edgeSet.ncard = L.edgeSet.ncard := by
  rw [le_antisymm hKL hLK]
