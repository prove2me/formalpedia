-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_separated_pair_with_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:05:01.565963+00:00
-- url     : https://prove2.me/submissions/7e49e01b-b620-46b8-b332-6291e7c32179
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge_from_components

set_option autoImplicit false

/-- Extend a planar drawing by inserting the unique edge between two components. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ G' : SimpleGraph V,
      G ≤ G' ∧ G'.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G'.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  obtain ⟨G', hle, hadj, hdraw, hedgeSet, hnew⟩ :=
    WilliamsonShmoys.planar_drawing_insert_edge_from_components
      G hG huv hUnreachable
  refine ⟨G', hle, hadj, hdraw, ?_⟩
  rw [hedgeSet]
  exact Set.ncard_insert_of_notMem hnew