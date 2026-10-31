-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:57.460761+00:00
-- url     : https://prove2.me/submissions/09cd1112-9e1e-4b6a-9152-144f9f95c9b5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    Q.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hRDraw, hCountLe, hRCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_18404f9f_9ab8_47a7_a1ab_ce02769fbc56_a1
      Q hDraw hV
  exact hCountLe.trans_eq hRCount