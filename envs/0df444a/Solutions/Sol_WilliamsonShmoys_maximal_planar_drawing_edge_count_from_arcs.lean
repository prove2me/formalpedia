-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_from_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:28:03.015483+00:00
-- url     : https://prove2.me/submissions/b586a063-c349-4884-b728-bc1c5b1aa4e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcard⟩ :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_extension K hK hV
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hcard