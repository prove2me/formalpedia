-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:30:33.60155+00:00
-- url     : https://prove2.me/submissions/22db7e99-e405-46c8-85ce-b83325e71855

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  have hCounts :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1
      K hK hV hMax
  cases hCounts with
  | intro f hCounts =>
    cases hCounts with
    | intro hEuler hIncidence => omega