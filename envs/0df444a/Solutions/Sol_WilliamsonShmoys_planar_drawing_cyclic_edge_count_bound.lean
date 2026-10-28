-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_cyclic_edge_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:43:23.281667+00:00
-- url     : https://prove2.me/submissions/048b936f-e364-4c87-b26d-dd60376c5fe4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_count
import Theorems.Thm_WilliamsonShmoys_euler_face_count_bound_arithmetic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCyclic : ¬ G.IsAcyclic) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hV : 3 ≤ Fintype.card V := by
    by_contra h
    apply hCyclic
    exact SimpleGraph.IsAcyclic.of_card_le_two (by simpa using (show Fintype.card V ≤ 2 by omega))
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_euler_face_count G hConnected hDrawing hV
  exact WilliamsonShmoys.euler_face_count_bound_arithmetic
    G.edgeSet.ncard (Fintype.card V) f hEuler hFaces