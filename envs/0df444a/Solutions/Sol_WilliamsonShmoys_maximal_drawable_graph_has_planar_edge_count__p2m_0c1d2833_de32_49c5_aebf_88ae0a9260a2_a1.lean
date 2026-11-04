-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:37.996968+00:00
-- url     : https://prove2.me/submissions/ba5870a9-cb3e-4140-93d5-ca2ab37b859c

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1 H hcard hH
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1 H hcard hH hmax
  omega