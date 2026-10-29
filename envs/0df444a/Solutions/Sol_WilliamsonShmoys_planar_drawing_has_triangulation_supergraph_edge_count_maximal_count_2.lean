-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:34:50.739085+00:00
-- url     : https://prove2.me/submissions/b2d91876-ab3c-4004-a96e-5bb0426b4c2e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_curve_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing M hV hM hmax
