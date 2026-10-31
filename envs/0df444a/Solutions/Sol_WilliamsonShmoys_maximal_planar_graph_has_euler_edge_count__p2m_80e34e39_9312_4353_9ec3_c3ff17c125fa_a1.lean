-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:24.411309+00:00
-- url     : https://prove2.me/submissions/ce26bddb-8420-4a87-abe0-e778122e70c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1 H hDraw hV
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1 H hDraw hV hMax
  omega