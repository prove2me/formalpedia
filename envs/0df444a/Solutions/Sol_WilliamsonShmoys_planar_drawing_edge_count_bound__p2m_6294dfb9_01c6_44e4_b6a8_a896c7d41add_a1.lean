-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:52:25.718393+00:00
-- url     : https://prove2.me/submissions/02d9e899-8e91-4bed-b40d-dd1a12c083c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424
set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V) :
    J.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hJK, hKConn, hKDraw, hEdgeCount⟩ :=
    planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
      J hDraw
  have hEuler := planar_edge_bound_for_face_accounting_57972424
    K hKDraw hKConn hCard
  omega