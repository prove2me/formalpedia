-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:17.738934+00:00
-- url     : https://prove2.me/submissions/5daa9148-9676-47fd-b3a4-2401a7f26fa5

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V = M.edgeFinset.card + 6) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1 M hV hM
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1 M hV hM hmax
  omega
