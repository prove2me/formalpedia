-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_f15616f1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:50:36.579991+00:00
-- url     : https://prove2.me/submissions/4e5445bc-1627-4f83-8909-f56c8a7ee20a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_equations

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
      H ≤ J → H = J) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_equations H hH hmax hCard
  omega