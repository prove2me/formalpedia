-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:21.872498+00:00
-- url     : https://prove2.me/submissions/b7623005-b6be-4c47-a04f-24a3d3b2b4cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
      G hG hcard
  omega