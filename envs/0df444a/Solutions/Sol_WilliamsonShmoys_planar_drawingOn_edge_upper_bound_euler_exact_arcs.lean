-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_upper_bound_euler_exact_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:33:53.438538+00:00
-- url     : https://prove2.me/submissions/8e5d5399-be5c-4875-b618-8dbb09ff7ece
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_augmentation_face_counts

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨m, f, hEdges, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_connected_augmentation_face_counts T hV hT
  omega