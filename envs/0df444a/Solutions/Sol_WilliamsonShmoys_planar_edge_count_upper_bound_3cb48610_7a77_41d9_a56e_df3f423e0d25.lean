-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:42:45.396471+00:00
-- url     : https://prove2.me/submissions/59c0f61b-b685-41d3-a28c-fb4540a8305a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 <= Fintype.card V) :
    R.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  rcases WilliamsonShmoys.planar_drawing_maximal_supergraph_fixed_vertices R hRdraw with
    ⟨H, hRsub, hHdraw, hHmax⟩
  have hbound := WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_bound
    H hHdraw hCard hHmax
  have hcard : R.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hRsub
  omega