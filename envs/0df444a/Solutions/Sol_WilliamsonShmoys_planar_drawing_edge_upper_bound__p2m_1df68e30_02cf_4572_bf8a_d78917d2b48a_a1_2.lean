-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:22.386609+00:00
-- url     : https://prove2.me/submissions/313543a0-4728-4ce5-90ba-4db210eaccbc

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_edge_count_upper_bound L hL hcard
