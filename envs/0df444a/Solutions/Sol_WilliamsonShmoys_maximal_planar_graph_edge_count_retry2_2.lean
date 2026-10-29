-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:24.447997+00:00
-- url     : https://prove2.me/submissions/b9ba895e-ca91-4518-ab84-34034fbb6901

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_curve_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing M hV hM hMax
