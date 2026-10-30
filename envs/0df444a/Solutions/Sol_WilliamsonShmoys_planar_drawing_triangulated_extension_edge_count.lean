-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:54:05.158353+00:00
-- url     : https://prove2.me/submissions/f516bad3-c13f-4958-8cdd-666d86326ea1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, N <= K /\ HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hKdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_finite N hdraw
  have hcount := WilliamsonShmoys.maximal_drawable_planar_graph_edge_count K hKdraw hV hmax
  exact ⟨K, hNK, hKdraw, hcount⟩