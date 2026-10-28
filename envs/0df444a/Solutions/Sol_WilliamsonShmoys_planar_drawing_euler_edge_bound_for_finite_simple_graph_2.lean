-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_euler_edge_bound_for_finite_simple_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:53:25.501985+00:00
-- url     : https://prove2.me/submissions/46f5a8bc-4417-41b9-b890-469bda7cf138
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_spanning_supergraph_of_at_least_three_vertices
import Theorems.Thm_WilliamsonShmoys_planar_connected_euler_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hsub, hconn, hH⟩ :=
    WilliamsonShmoys.planar_connected_spanning_supergraph_of_at_least_three_vertices
      G hG hcard
  have hbound :=
    WilliamsonShmoys.planar_connected_euler_edge_bound H hH hconn hcard
  have hle : G.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hsub
  omega