-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:44:44.433992+00:00
-- url     : https://prove2.me/submissions/93af9d7a-651b-426a-95f1-e38e33728373
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hconn, hplanar, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_connected L hL
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound H hplanar hconn hV
  omega