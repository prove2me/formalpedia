-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:26:34.242095+00:00
-- url     : https://prove2.me/submissions/0d9440f0-f490-4e64-8929-4caea5343fd3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4 G hDraw hV
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4 H hDrawH hV hMax
  have hEdge : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hSub
  omega