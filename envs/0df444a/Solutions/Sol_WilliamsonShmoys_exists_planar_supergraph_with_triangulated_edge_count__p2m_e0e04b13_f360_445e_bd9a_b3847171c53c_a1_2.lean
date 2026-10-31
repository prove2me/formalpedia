-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:45.461994+00:00
-- url     : https://prove2.me/submissions/13143eea-5cd6-44ea-afa5-5e9c70e1d9eb

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_b65312a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_drawing_triangulated_extension_b65312a2 G hV hG
