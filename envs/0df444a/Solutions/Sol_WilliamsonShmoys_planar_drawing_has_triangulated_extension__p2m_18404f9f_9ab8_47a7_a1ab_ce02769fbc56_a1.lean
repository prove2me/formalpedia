-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:49.139572+00:00
-- url     : https://prove2.me/submissions/883b3a0c-2f58-48a1-9c0b-72ae181cf4be

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ HasPlanarDrawingOn R ∧
      Q.edgeSet.ncard ≤ R.edgeSet.ncard ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hRDraw, hRMax, hEdgeMono⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
      Q hDraw hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
      R hRDraw hV hRMax
  exact ⟨R, hQR, hRDraw, hEdgeMono, hCount⟩