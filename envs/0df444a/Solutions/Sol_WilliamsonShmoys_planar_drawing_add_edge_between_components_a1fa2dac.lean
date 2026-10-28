-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_components_a1fa2dac
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:37:22.578404+00:00
-- url     : https://prove2.me/submissions/66c28a71-a3f6-4c31-b2de-829c746faaf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_exists_not_reachable_of_not_connected
import Theorems.Thm_WilliamsonShmoys_planar_augment_between_unreachable_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.exists_not_reachable_of_not_connected G hDisconnected
  exact WilliamsonShmoys.planar_augment_between_unreachable_vertices G hG huv