-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:47.287703+00:00
-- url     : https://prove2.me/submissions/bc5f362e-75ad-4e7b-9a29-a20d92cdd1f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1 H hDraw hV