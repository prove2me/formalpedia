-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:46:51.334899+00:00
-- url     : https://prove2.me/submissions/e70a6aca-97da-4128-8cae-1771cd148aff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLdraw, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_maximal_extension K hdraw
  refine ⟨L, hKL, hLdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count
    L hV hLdraw hmax