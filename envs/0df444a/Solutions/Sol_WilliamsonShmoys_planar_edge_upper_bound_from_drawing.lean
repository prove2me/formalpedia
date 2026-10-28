-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_from_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:21:29.094286+00:00
-- url     : https://prove2.me/submissions/ba6d6ee7-fdd3-4733-ae30-81d7413bff7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_same_vertex_edge_completion_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK⟩ :=
    WilliamsonShmoys.planar_drawing_same_vertex_edge_completion_bound H hV hH
  have hedge : H.edgeSet ⊆ K.edgeSet := by
    intro e he
    exact hHK he
  have hn : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_le_ncard hedge
  omega