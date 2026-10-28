-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:39:58.071584+00:00
-- url     : https://prove2.me/submissions/d1b86444-d5e9-4923-878f-2538175bf480
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_equations_for_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_euler_face_equations_for_bound K hDraw hMax hCard
  omega