-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_completion_edge_lower_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:45.774884+00:00
-- url     : https://prove2.me/submissions/1dbdc242-a605-4913-bcb3-99fd782b0843
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ HasPlanarDrawingOn H ∧
        3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hHDraw, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
      G hDraw
  obtain hcount :=
    WilliamsonShmoys.planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
      H hHDraw hmax hV
  exact ⟨H, hGH, hHDraw, hcount⟩