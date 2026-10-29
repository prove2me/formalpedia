-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_edge_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:52:13.829353+00:00
-- url     : https://prove2.me/submissions/215c2c11-0ae1-49fa-afb9-12c6e7fc92c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_same_vertex_set_d3f6855c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hStrict : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ (L = K -> False) /\
        WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hEdges, hPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_same_vertex_set_d3f6855c K hV hK
  refine ⟨L, hKL, ?_, hPlanar⟩
  intro hEq
  subst L
  omega