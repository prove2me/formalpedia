-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:12.481508+00:00
-- url     : https://prove2.me/submissions/9c3f000c-16cd-49bf-8ac5-f4efe0cfe4da

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHdraw, hcard, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
      H hHdraw hV hmax
  exact ⟨H, hGH, hHdraw, hcard, hcount⟩