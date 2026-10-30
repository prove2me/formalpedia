-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_a305a22a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:41:58.845269+00:00
-- url     : https://prove2.me/submissions/a4073623-b162-44d7-b197-2dea9b905fd6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_a305a22a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_a305a22a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawable_edge_count_upper_a305a22a K hV hK
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_a305a22a
    K hV hK hmax
  omega