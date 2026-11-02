-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:52:05.878205+00:00
-- url     : https://prove2.me/submissions/c2f8be6e-61c6-42e6-bd18-031d5a79aaf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_a6656023_52ae_443d_ab7b_e0c464fa9c80_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M ≤ N → N = M) :
    3 * Fintype.card V - 6 ≤
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card) := by
  exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_a6656023_52ae_443d_ab7b_e0c464fa9c80_a1
    M hcard hM