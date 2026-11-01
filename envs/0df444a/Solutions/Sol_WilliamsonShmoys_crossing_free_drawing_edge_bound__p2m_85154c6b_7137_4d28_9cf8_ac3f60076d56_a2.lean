-- Prove2me | solution 1 for WilliamsonShmoys.crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:15.503066+00:00
-- url     : https://prove2.me/submissions/14e62d4a-8b3e-4a4d-8f4c-fbbd3c4f2b9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hcount, hdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
      H hH hconn hcard
  have hKcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
      K hdraw hmax hcard
  omega