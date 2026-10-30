-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:13:11.564539+00:00
-- url     : https://prove2.me/submissions/9396e4e4-7fb2-4d54-80be-02bedf57ddee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, _hH, hEdgeCount, hEdgeLe⟩ :=
    WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1
      K hK hV
  omega