-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_same_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:17:57.039011+00:00
-- url     : https://prove2.me/submissions/5142110b-947b-40bc-ae5a-60aa05e36839
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion_same_vertices_v4
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion_same_vertices_v3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJdraw, hJconn⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion_same_vertices_v4
      H hV hdraw
  obtain ⟨K, hJK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.connected_planar_triangulation_completion_same_vertices_v3
      J hV hJdraw hJconn
  exact ⟨K, le_trans hHJ hJK, hKdraw, hKcount⟩