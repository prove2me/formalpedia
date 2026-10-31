-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:55.769239+00:00
-- url     : https://prove2.me/submissions/0858dc3f-8b05-455c-91dd-79fea1a03542

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
import Theorems.Thm_WilliamsonShmoys_drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hH, hLH, hCount, hMax⟩ :=
    WilliamsonShmoys.drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
      L hL
  have hEq :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
      H hH hCard hMax
  calc
    L.edgeSet.ncard + 6 ≤ H.edgeSet.ncard + 6 :=
      Nat.add_le_add_right hCount 6
    _ = 3 * Fintype.card V := hEq