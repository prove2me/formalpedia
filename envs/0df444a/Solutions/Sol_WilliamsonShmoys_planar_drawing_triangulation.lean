-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:45:14.906689+00:00
-- url     : https://prove2.me/submissions/d064a291-eeb8-46d3-8c46-c366d42a3d4a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_maximal_for_triangulation
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hconn : P.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet ⊆ Q.edgeSet ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hQ, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_extension_maximal_for_triangulation P hdraw
  refine ⟨Q, hQ, hsub, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulation Q hQ hV hmax
