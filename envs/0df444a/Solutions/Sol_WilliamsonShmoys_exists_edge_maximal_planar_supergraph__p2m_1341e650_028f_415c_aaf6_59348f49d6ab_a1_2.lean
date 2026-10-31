-- Prove2me | solution 2 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:49.654983+00:00
-- url     : https://prove2.me/submissions/b1c88819-b9d6-4aef-a638-ad45590cc830

import Theorems.Thm_WilliamsonShmoys_planar_extension_to_maximal_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet :=
  WilliamsonShmoys.planar_extension_to_maximal_drawing H hH
