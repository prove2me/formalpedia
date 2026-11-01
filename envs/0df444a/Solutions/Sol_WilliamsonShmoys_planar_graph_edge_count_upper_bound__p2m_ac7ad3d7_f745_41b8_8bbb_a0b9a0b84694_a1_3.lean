-- Prove2me | solution 3 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:15.091058+00:00
-- url     : https://prove2.me/submissions/9d67422b-7c0f-4105-8095-a8b53536805b

import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.exists_drawable_edge_count_upper_bound G hcard hplanar
