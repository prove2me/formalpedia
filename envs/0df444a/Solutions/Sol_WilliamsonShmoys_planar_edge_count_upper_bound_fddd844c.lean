-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_fddd844c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:58:44.737415+00:00
-- url     : https://prove2.me/submissions/c530e40b-1451-468d-8e18-468fe35249f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_fddd844c
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_fddd844c

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨N, hNconn, hNplanar, hSub, hCount⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_fddd844c M hM hCard
  have hN := WilliamsonShmoys.connected_planar_edge_count_bound_fddd844c
    N hNplanar hNconn hCard
  omega