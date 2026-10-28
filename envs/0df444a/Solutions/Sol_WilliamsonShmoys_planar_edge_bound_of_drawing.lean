-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:49:47.407218+00:00
-- url     : https://prove2.me/submissions/dd392924-0ac0-4691-8d33-a976407cbde6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximizer
import Theorems.Thm_WilliamsonShmoys_maximal_drawn_simple_graph_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax, hcount⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximizer G hG
  have hbound :=
    WilliamsonShmoys.maximal_drawn_simple_graph_edge_bound H hV hH hmax
  omega