-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:49:46.209466+00:00
-- url     : https://prove2.me/submissions/c27dd49e-f9c7-4dc7-817d-472548dcc57e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_upper_b94a5187
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_lower_b94a5187

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKdraw : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.maximal_drawable_supergraph_edge_count_upper_b94a5187 K hV hKdraw
  have hlo := WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_b94a5187 K hV hKdraw hmax
  omega