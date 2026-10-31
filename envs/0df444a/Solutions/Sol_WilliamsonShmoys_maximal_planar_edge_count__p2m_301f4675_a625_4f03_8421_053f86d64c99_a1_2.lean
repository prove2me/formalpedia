-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_301f4675_a625_4f03_8421_053f86d64c99_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:21:45.02753+00:00
-- url     : https://prove2.me/submissions/4e62091f-3035-4aa0-8172-6fef9e0d347f

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_triangulated_extension_b65312a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V = G.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulated_extension_b65312a2 G hV hG hmax
