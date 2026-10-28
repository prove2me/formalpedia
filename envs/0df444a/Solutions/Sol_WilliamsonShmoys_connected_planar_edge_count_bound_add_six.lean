-- Prove2me | solution 1 for WilliamsonShmoys_connected_planar_edge_count_bound_add_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:14:34.332985+00:00
-- url     : https://prove2.me/submissions/3d10694b-7af1-465f-b5f7-49ecf2bb5753
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_exists_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hH, hmax, hinc⟩ :=
    WilliamsonShmoys.planar_drawingOn_exists_maximal_planar_supergraph
      G hG hconn hcard
  have hEq := WilliamsonShmoys.maximal_planar_supergraph_edge_count
    H hH hmax hcard
  calc
    G.edgeSet.ncard + 6 ≤ H.edgeSet.ncard + 6 := Nat.add_le_add_right hinc 6
    _ = 3 * Fintype.card V := hEq