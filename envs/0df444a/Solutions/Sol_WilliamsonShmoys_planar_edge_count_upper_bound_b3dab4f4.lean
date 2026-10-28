-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_b3dab4f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:54:05.127915+00:00
-- url     : https://prove2.me/submissions/c984c7d3-6dca-4f23-a63f-091b1cc48976
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected_core_repair
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_repair

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hcount, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_connected_extension_repair L hV hL
  exact hcount.trans
    (WilliamsonShmoys.planar_edge_count_connected_core_repair
      H hV hconn hplanar)