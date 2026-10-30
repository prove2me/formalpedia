-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:35.151166+00:00
-- url     : https://prove2.me/submissions/9375fa4a-d136-473d-91b9-a1f6efeadb27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1 K hK hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1 K hK hV hmax
  omega