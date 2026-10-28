-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_501982a3_cf58_468c_be32_1d2a30e3e83a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:05:51.323624+00:00
-- url     : https://prove2.me/submissions/9dc2caed-85dd-4154-94a9-89e5bd8372f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_a76877fd_7551_4249_899d_5acc3f351e6a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_equations_a76877fd_7551_4249_899d_5acc3f351e6a
      N hDraw hMax hV
  omega