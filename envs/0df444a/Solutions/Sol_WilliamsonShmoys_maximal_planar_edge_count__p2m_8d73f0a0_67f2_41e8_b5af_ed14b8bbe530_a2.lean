-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:55.397066+00:00
-- url     : https://prove2.me/submissions/94841106-45fd-4cca-a6fd-60c22fc8e47d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1 L hL hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1 L hL hcard hmax
  omega