-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:19.807461+00:00
-- url     : https://prove2.me/submissions/dbde2e7f-0c7e-4d0a-b81c-10157477a3ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hHplanar : HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ H.edgeSet ⊆ T.edgeSet ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hHT, hEdges, hTplanar, hmax⟩ := WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1 H hV hHplanar
  exact ⟨T, hHT, hEdges, WilliamsonShmoys.maximal_planar_edge_count__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1 T hV hTplanar hmax⟩
