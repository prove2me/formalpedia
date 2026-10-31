-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:26.088988+00:00
-- url     : https://prove2.me/submissions/3beec2f3-3a42-4593-a60c-457937175ede

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ HasPlanarDrawingOn S ∧
      S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨S, hRS, hDrawS, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
      R hDraw hV
  exact ⟨S, hRS, hDrawS,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
      S hDrawS hV hMax⟩