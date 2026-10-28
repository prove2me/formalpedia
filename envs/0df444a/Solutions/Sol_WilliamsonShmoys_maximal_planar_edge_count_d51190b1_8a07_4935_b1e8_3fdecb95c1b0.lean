-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:37:46.186195+00:00
-- url     : https://prove2.me/submissions/57bbaf64-bbd9-4342-84a9-123739227df8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_extension_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_triangulation_extension_v2 K hK hCard
  have hLK : L = K := hMax L hKL hL
  simpa [hLK] using hEdges