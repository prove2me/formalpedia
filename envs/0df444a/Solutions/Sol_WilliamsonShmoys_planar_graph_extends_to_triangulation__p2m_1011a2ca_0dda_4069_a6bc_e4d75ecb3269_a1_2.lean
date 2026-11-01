-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:09.047007+00:00
-- url     : https://prove2.me/submissions/75664976-9f58-45d2-94d2-3179ab0a9899

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_drawing_has_triangulation K hK hcard
