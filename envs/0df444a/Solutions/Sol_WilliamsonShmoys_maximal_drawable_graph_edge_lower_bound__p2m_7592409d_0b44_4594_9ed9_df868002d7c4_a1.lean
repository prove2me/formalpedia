-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:30.118116+00:00
-- url     : https://prove2.me/submissions/68ca145b-200f-4437-8755-f4270895dc9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
import Theorems.Thm_WilliamsonShmoys_triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, htri⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1 H hH hmax hV
  exact WilliamsonShmoys.triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1 (Fintype.card V) H.edgeSet.ncard f hV hEuler htri