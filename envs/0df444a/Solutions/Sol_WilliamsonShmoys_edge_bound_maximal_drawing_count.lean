-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_maximal_drawing_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:28:39.427536+00:00
-- url     : https://prove2.me/submissions/6a530cd9-2dfe-4afd-94bc-0ca281317bc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangle_incidence

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.maximal_planar_euler_face_count
    H hDraw hMax hCard
  have hIncidence := WilliamsonShmoys.maximal_planar_triangle_incidence
    H hDraw hMax hCard f hEuler
  omega