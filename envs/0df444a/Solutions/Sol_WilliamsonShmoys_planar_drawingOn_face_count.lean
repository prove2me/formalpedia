-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:20:35.224005+00:00
-- url     : https://prove2.me/submissions/b5997e13-022b-4449-812f-72ec82b4d435
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V)
    (hConnected : J.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = J.edgeSet.ncard + 2 ∧
      3 * f <= 2 * J.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
      J hDraw hConnected
  have hEdges :=
    WilliamsonShmoys.planar_drawing_edge_count_bound__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
      J hDraw hCard
  exact ⟨f, hEuler, by omega⟩