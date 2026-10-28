-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:29:23.188501+00:00
-- url     : https://prove2.me/submissions/700dbc8b-62b6-49c4-9989-275b542d415f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_repair_3e188728
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_repair_3e188728

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hCard : 3 <= Fintype.card V) :
    Y.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hconn, hdraw, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_repair_3e188728 Y hY
      (by omega : 0 < Fintype.card V)
  have hbound := WilliamsonShmoys.connected_planar_edge_bound_repair_3e188728
    H hconn hdraw hCard
  omega