-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_edge_bound_for_finite_simple_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:49:29.785227+00:00
-- url     : https://prove2.me/submissions/7f705597-bfd3-4476-8e1a-0f2152649fb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_spanning_supergraph
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
    WilliamsonShmoys.planar_connected_spanning_supergraph G hG
  have hbound :=
    WilliamsonShmoys.planar_connected_euler_edge_bound H hH hconn hcard
  have hle : G.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hsub
  omega