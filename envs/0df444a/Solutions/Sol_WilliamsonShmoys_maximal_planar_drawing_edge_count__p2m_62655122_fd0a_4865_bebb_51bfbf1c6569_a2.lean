-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:16:19.112779+00:00
-- url     : https://prove2.me/submissions/67727ae4-8b9b-462d-b760-b8b1a29f87fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M ≤ N → N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) = 3 * Fintype.card V - 6 := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
    M hcard hM
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
    M hcard hM hmax
  omega