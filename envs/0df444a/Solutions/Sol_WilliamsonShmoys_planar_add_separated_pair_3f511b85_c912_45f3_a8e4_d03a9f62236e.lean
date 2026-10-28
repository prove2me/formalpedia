-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:06:52.602299+00:00
-- url     : https://prove2.me/submissions/acbd4cc9-9c3c-4881-a06a-45fb69c1402c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_separated_pair_with_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧
      HasPlanarDrawingOn G' ∧
      G.edgeSet.ncard < G'.edgeSet.ncard := by
  obtain ⟨G', hsub, hadj, hplanar, hcard⟩ :=
    planar_drawing_add_separated_pair_with_edge_count G hG huv hUnreachable
  refine ⟨G', hsub, hplanar, ?_⟩
  omega