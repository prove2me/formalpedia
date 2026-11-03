-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:30:58.31881+00:00
-- url     : https://prove2.me/submissions/9ff09bf8-d810-4642-95d2-8336ea535788

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
import Theorems.Thm_WilliamsonShmoys_euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, _hHK, hEdges, f, l, hEuler, hSides, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
      H hcard hH
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hBound :=
    WilliamsonShmoys.euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
      (Fintype.card V) K.edgeFinset.card f l hcard hEuler hSides hFaces
  omega