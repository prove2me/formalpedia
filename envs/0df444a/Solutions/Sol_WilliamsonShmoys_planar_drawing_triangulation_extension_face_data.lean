-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:43:11.139144+00:00
-- url     : https://prove2.me/submissions/3220cf8c-a036-4745-b87c-7dfa6f256247

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_face_data
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_from_face_data

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJDraw, hJMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_face_data H hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_face_data
      J hJDraw hCard hJMax
  exact ⟨J, hHJ, hJDraw, hCount⟩