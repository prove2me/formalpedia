-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:27.655046+00:00
-- url     : https://prove2.me/submissions/8d3f4ad7-717d-4a3f-a985-1f1465ee0a37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
import Theorems.Thm_finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  refine finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
    (fun G => WilliamsonShmoys.HasPlanarDrawingOn G) H hDraw ?_
  intro G hG hDisconnected
  exact WilliamsonShmoys.planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
    G hG hDisconnected