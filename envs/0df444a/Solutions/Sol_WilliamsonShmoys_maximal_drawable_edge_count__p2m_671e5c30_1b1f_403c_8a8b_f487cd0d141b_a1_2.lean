-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:39.770889+00:00
-- url     : https://prove2.me/submissions/55207480-33f9-410d-adcd-1ec716386f5f

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_euler_v2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2 K hK hmax hV
