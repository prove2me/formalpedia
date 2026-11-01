-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:01.191494+00:00
-- url     : https://prove2.me/submissions/dc1c6f9d-32a9-49cd-99e8-73fe5fb27fcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
import Theorems.Thm_WilliamsonShmoys_planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1

set_option autoImplicit false

open Finset

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨C, hdisj, hcover, hedges, hlocal⟩ :=
    WilliamsonShmoys.planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
      L hL
  exact WilliamsonShmoys.planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
    L C hdisj hcover hedges hlocal hcard