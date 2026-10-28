-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:50:17.47075+00:00
-- url     : https://prove2.me/submissions/e61c669c-c7a5-4378-a1a3-8a2614ea9558
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hcount, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
      L hL
  exact le_trans hcount
    (WilliamsonShmoys.maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
      H hV hH hmax)
