-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_with_three_vertices__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:11.276152+00:00
-- url     : https://prove2.me/submissions/88fb07ee-c623-43da-89b9-b7851d83b006
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_step__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hsub, hplanar, hconn⟩ :=
    WilliamsonShmoys.finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
      H WilliamsonShmoys.HasPlanarDrawingOn hDraw (by
        intro G hG hnot
        exact WilliamsonShmoys.planar_drawing_connected_extension_step__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
          G hV hG hnot)
  exact ⟨K, hsub, hconn, hplanar⟩