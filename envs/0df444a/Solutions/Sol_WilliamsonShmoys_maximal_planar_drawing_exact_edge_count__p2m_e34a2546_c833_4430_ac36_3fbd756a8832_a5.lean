-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:30:37.443578+00:00
-- url     : https://prove2.me/submissions/f290e5b9-e9a3-4c75-a70a-278b067d8232

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
    M hM hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
    M hM hV hMmax
  omega