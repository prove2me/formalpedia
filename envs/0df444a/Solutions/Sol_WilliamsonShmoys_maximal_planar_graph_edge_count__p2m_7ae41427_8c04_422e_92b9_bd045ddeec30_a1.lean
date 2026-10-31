-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:35.410626+00:00
-- url     : https://prove2.me/submissions/946bd953-9b41-45ab-b34b-29cb4cbe1188

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2
      H hH hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2
      H hH hCard hMax
  omega