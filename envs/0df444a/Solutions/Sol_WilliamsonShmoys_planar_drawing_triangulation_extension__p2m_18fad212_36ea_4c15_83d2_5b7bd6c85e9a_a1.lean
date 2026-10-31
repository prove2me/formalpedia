-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:43.233124+00:00
-- url     : https://prove2.me/submissions/0c92c68d-c1a4-4fbd-ba2a-4ee4931bc341

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hHL, hLDraw, hLmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
      H hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
      L hLDraw hV hLmax
  exact ⟨L, hHL, hLDraw, hCount⟩