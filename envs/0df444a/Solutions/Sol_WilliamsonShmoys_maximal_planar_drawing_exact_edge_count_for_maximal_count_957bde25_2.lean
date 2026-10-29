-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:33:16.537284+00:00
-- url     : https://prove2.me/submissions/1026bca2-fb21-4b92-97b6-740ffa3f57e2

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_curve_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing K hV hK hKmax
