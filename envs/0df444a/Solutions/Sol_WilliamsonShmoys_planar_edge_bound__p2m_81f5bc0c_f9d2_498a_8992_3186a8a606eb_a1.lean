-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:32:22.367123+00:00
-- url     : https://prove2.me/submissions/4e598509-b196-41e6-8884-e032aab6c737
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hconn, hdraw, hEdges⟩ :=
    WilliamsonShmoys.connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
      N hN
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
      H hCard hconn hdraw
  omega