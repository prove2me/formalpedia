-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:45.941279+00:00
-- url     : https://prove2.me/submissions/daebd8fc-929c-42ee-82a7-d2f503e6e933

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count H hH hV
