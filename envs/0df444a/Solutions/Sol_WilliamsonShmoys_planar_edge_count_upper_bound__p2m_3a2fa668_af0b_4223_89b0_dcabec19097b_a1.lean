-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:47.578593+00:00
-- url     : https://prove2.me/submissions/fdfd4ffb-58fb-490f-9438-367c21d79b1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hEdges, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
      G hG hCard
  calc
    G.edgeSet.ncard <= H.edgeSet.ncard := hEdges
    _ = 3 * Fintype.card V - 6 := hMax